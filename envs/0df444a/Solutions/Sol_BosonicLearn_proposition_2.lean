-- Prove2me | solution 1 for BosonicLearn.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T04:12:19.992815+00:00
-- url     : https://prove2.me/submissions/2c56f868-240a-46d7-bbf1-1e7fb2aa03ba

/-
Proof-sketch of BosonicLearn.proposition_2.
All local helper theorems are proved. The single Open dependency is
SpectrumLB.eq_7_14, the existing Haar-unitary concentration theorem.
Lean v4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp
import Theorems.Thm_BosonicLearn_gammaFock_mul
import Theorems.Thm_BosonicLearn_gammaFock_posSemidef
import Definitions.Def_BosonicLearn_PhiMap
import Definitions.Def_BosonicLearn_Ggood
import Definitions.Def_BosonicLearn_herm0Ball
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Definitions.Def_WHMultiplicativity_schattenNorm
import Definitions.Def_BosonicLearn_Herm0
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Definitions.Def_BosonicLearn_priorMu
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Theorems.Thm_SpectrumLB_eq_7_14

set_option autoImplicit false

/- Local helper source: Solutions.Prop5PhotonMoment -/
section
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder
open BosonicLearn
noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 1000000

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
theorem gammaFock_diagonal_self {n : ℕ} (c : Fin n → ℂ) (u : Fin n → ℕ) :
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

theorem gammaFock_diagonal_re {n : ℕ} (d : Fin n → ℝ) (u : Fin n → ℕ) :
    (gammaFock (Matrix.diagonal fun i => (d i : ℂ)) u u).re = ∏ i, d i ^ u i := by
  simp only [gammaFock_diagonal_self, ← Complex.ofReal_pow, ← Complex.ofReal_prod,
    Complex.ofReal_re]


/-- The second moment series of an unnormalized geometric distribution. -/
theorem hasSum_sq_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * r ^ k) (r * (1 + r) / (1 - r) ^ 3) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  have hne : 1 - r ≠ 0 := by linarith
  have hc := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr).mul_left 2
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr).mul_left 3
  have h0 := (hasSum_geometric_of_lt_one hr0 hr1).mul_left 2
  have hcval (k : ℕ) : 2 * (((k + 2).choose 2 : ℕ) : ℝ) =
      (k : ℝ) ^ 2 + 3 * k + 2 := by
    have hnat : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
      rw [Nat.choose_two_right]
      have heven := Nat.even_mul_pred_self (k + 2)
      simpa [Nat.add_sub_cancel] using (Nat.mul_div_cancel' heven.two_dvd)
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast at hcast
    nlinarith
  have h := (hc.sub h1).sub h0
  have hval : 2 * (1 / (1 - r) ^ (2 + 1)) - 3 * (r / (1 - r) ^ 2) -
      2 * (1 - r)⁻¹ = r * (1 + r) / (1 - r) ^ 3 := by
    field_simp
    ring
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  have hh := hcval k
  linear_combination -r ^ k * hh

/-- Mean and second moment of the geometric law on `0,1,…`. -/
theorem geometric_moments {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (1 - r) * r ^ k) 1 ∧
    HasSum (fun k : ℕ => (k : ℝ) * ((1 - r) * r ^ k)) (r / (1 - r)) ∧
    HasSum (fun k : ℕ => (k : ℝ) ^ 2 * ((1 - r) * r ^ k))
      (r / (1 - r) + 2 * (r / (1 - r)) ^ 2) := by
  have hne : 1 - r ≠ 0 := by linarith
  have hr : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr0] using hr1
  constructor
  · have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 - r)
    rwa [mul_inv_cancel₀ hne] at h
  constructor
  · have h := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hr).mul_left (1 - r)
    have hv : (1 - r) * (r / (1 - r) ^ 2) = r / (1 - r) := by field_simp
    rw [hv] at h
    exact h.congr_fun fun k => by ring
  · have h := (hasSum_sq_mul_geometric hr0 hr1).mul_left (1 - r)
    have hv : (1 - r) * (r * (1 + r) / (1 - r) ^ 3) =
        r / (1 - r) + 2 * (r / (1 - r)) ^ 2 := by field_simp; ring
    rw [hv] at h
    exact h.congr_fun fun k => by ring

private lemma hasSum_pair_nonneg {A B : Type} {f : A → ℝ} {g : B → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    HasSum (fun p : A × B => f p.1 * g p.2) (a * b) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable hf0 hg0)

/-- First and second moments add in the usual way for independent discrete coordinates. -/
theorem independent_sum_moments (n : ℕ) :
    ∀ (p : Fin n → ℕ → ℝ) (m v : Fin n → ℝ),
      (∀ i k, 0 ≤ p i k) →
      (∀ i, HasSum (p i) 1) →
      (∀ i, HasSum (fun k : ℕ => (k : ℝ) * p i k) (m i)) →
      (∀ i, HasSum (fun k : ℕ => (k : ℝ) ^ 2 * p i k) (v i + (m i) ^ 2)) →
      HasSum (fun u : Fin n → ℕ => ∏ i, p i (u i)) 1 ∧
      HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) * ∏ i, p i (u i)) (∑ i, m i) ∧
      HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 * ∏ i, p i (u i))
        ((∑ i, v i) + (∑ i, m i) ^ 2) := by
  induction n with
  | zero =>
    intro p m v _ _ _ _
    simp
  | succ n ih =>
    intro p m v hp h0 h1 h2
    obtain ⟨hP, hM, hS⟩ := ih (fun i => p i.succ) (fun i => m i.succ) (fun i => v i.succ)
      (fun i k => hp i.succ k) (fun i => h0 i.succ)
      (fun i => h1 i.succ) (fun i => h2 i.succ)
    have hp0 : ∀ u : Fin n → ℕ, 0 ≤ ∏ i, p i.succ (u i) :=
      fun u => Finset.prod_nonneg fun i _ => hp i.succ (u i)
    have hm0 : ∀ u : Fin n → ℕ, 0 ≤ (∑ i, (u i : ℝ)) * ∏ i, p i.succ (u i) :=
      fun u => mul_nonneg (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _) (hp0 u)
    have hs0 : ∀ u : Fin n → ℕ, 0 ≤ (∑ i, (u i : ℝ)) ^ 2 * ∏ i, p i.succ (u i) :=
      fun u => mul_nonneg (sq_nonneg _) (hp0 u)
    have hk1 : ∀ k : ℕ, 0 ≤ (k : ℝ) * p 0 k := fun k => mul_nonneg (Nat.cast_nonneg _) (hp 0 k)
    have hk2 : ∀ k : ℕ, 0 ≤ (k : ℝ) ^ 2 * p 0 k := fun k => mul_nonneg (sq_nonneg _) (hp 0 k)
    constructor
    · have h := hasSum_pair_nonneg (h0 0) hP (hp 0) hp0
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
      convert h using 1
      · ext u
        simp [Fin.consEquiv, Fin.prod_univ_succ]
      · norm_num
    constructor
    · have h := (hasSum_pair_nonneg (h1 0) hP hk1 hp0).add
        (hasSum_pair_nonneg (h0 0) hM (hp 0) hm0)
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
      convert h using 1
      · ext u
        simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.sum_univ_succ]
        ring
      · simp [Fin.sum_univ_succ]
    · have h := ((hasSum_pair_nonneg (h2 0) hP hk2 hp0).add
        ((hasSum_pair_nonneg (h1 0) hM hk1 hm0).mul_left 2)).add
          (hasSum_pair_nonneg (h0 0) hS (hp 0) hs0)
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff]
      convert h using 1
      · ext u
        simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.sum_univ_succ]
        ring
      · simp only [Fin.sum_univ_succ]
        ring

/-- The second moment of a sum of independent geometric occupations. -/
theorem geometric_sum_second_moment {n : ℕ} (d : Fin n → ℝ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    HasSum (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 *
      ∏ i, ((1 - d i) * d i ^ u i))
      ((∑ i, (d i / (1 - d i) + (d i / (1 - d i)) ^ 2)) +
        (∑ i, d i / (1 - d i)) ^ 2) := by
  apply (independent_sum_moments n
    (fun i k => (1 - d i) * d i ^ k)
    (fun i => d i / (1 - d i))
    (fun i => d i / (1 - d i) + (d i / (1 - d i)) ^ 2)
    (fun i k => mul_nonneg (by linarith [hd1 i]) (pow_nonneg (hd0 i) k))
    (fun i => (geometric_moments (hd0 i) (hd1 i)).1)
    (fun i => (geometric_moments (hd0 i) (hd1 i)).2.1)
    (fun i => ?_)).2.2
  convert (geometric_moments (hd0 i) (hd1 i)).2.2 using 1
  ring

/-- The actual diagonal Born weights have the same total photon moments as the eigenmode geometries. -/
theorem hasSum_photon_second_moment {n : ℕ} (R U : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℝ) (hR : R.PosSemidef) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (hspec : R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)
    (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i < 1) :
    HasSum (fun u : Occupation (Fin n) => (∑ i, (u i : ℝ)) ^ 2 * (fugacityCoeff R u u).re)
      ((∑ i, (d i / (1 - d i) + (d i / (1 - d i)) ^ 2)) +
        (∑ i, d i / (1 - d i)) ^ 2) := by
  have hdet : (1 - R).det = ((∏ i, (1 - d i) : ℝ) : ℂ) := by
    rw [hspec, one_sub_conj U _ hU2, one_sub_diagonal, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul, hU2, Matrix.det_one, one_mul,
      Complex.ofReal_prod]
  have hpos : 0 < ∏ i, (1 - d i) := Finset.prod_pos fun i _ => by linarith [hd1 i]
  have hx : ∀ u, (fugacityCoeff R u u).re = (∏ i, (1 - d i)) * (gammaFock R u u).re := by
    intro u
    unfold fugacityCoeff
    rw [Matrix.smul_apply, smul_eq_mul, hdet, Complex.re_ofReal_mul]
  have hx0 : ∀ u, 0 ≤ (fugacityCoeff R u u).re := fun u => by
    rw [hx]
    exact mul_nonneg hpos.le (gammaFock_diag_real R hR u).2
  have hsec0 : ∀ N, ∑ u ∈ sec n N, (gammaFock R u u).re =
      ∑ u ∈ sec n N, ∏ i, d i ^ u i := by
    intro N
    have h := sector_trace_comm (U * Matrix.diagonal (fun i => (d i : ℂ))) Uᴴ N
    rw [← hspec, ← Matrix.mul_assoc, hU1, Matrix.one_mul] at h
    rw [← Complex.re_sum, h, Complex.re_sum]
    exact Finset.sum_congr rfl fun u _ => gammaFock_diagonal_re d u
  apply hasSum_of_sector
    (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 * (fugacityCoeff R u u).re)
    (fun u : Fin n → ℕ => (∑ i, (u i : ℝ)) ^ 2 * ∏ i, ((1 - d i) * d i ^ u i))
    (fun u => mul_nonneg (sq_nonneg _) (hx0 u))
    (fun u => mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ =>
      mul_nonneg (by linarith [hd1 i]) (pow_nonneg (hd0 i) _)))
    ?_ (geometric_sum_second_moment d hd0 hd1)
  intro N
  have hc : ∀ x : (Fin n → ℕ) → ℝ,
      ∑ u ∈ sec n N, (∑ i, (u i : ℝ)) ^ 2 * ((∏ i, (1 - d i)) * x u) =
        ((N : ℝ) ^ 2 * ∏ i, (1 - d i)) * ∑ u ∈ sec n N, x u := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← Nat.cast_sum, (mem_sec u).mp hu]
    ring
  simp_rw [hx, Finset.prod_mul_distrib]
  rw [hc, hc, hsec0 N]

private lemma diagonal_upper_bound {n : ℕ} (R U : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℝ) (b : ℝ) (hU1 : Uᴴ * U = 1)
    (hspec : R = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ)
    (hb : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R).PosSemidef) :
    ∀ i, d i ≤ b := by
  have h := hb.conjTranspose_mul_mul_same U
  have heq : Uᴴ * ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R) * U =
      Matrix.diagonal (fun i => ((b - d i : ℝ) : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hU1]
    have heq' : Uᴴ * R * U = Matrix.diagonal (fun i => (d i : ℂ)) := by
      rw [hspec]
      calc Uᴴ * (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) * U =
          (Uᴴ * U) * Matrix.diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
    rw [heq', ← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    ext i
    simp
  rw [heq, Matrix.posSemidef_diagonal_iff] at h
  intro i
  have hi := Complex.zero_le_real.mp (h i)
  linarith

/-- The scalar estimate used in Eq. (92), with room in its numerical constant. -/
theorem occupation_moment_bound {n : ℕ} (ν : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (m : Fin n → ℝ)
    (hm0 : ∀ i, 0 ≤ m i) (hm1 : ∀ i, m i ≤ 2 * ν) :
    (∑ i, (m i + (m i) ^ 2)) + (∑ i, m i) ^ 2 ≤ 12 * ν ^ 2 * n ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  have hnν : 1 ≤ ν * n := (div_le_iff₀ hn0).mp hν
  have hm_sq : ∀ i, (m i) ^ 2 ≤ 4 * ν ^ 2 := by
    intro i
    nlinarith [hm0 i, hm1 i]
  have hv : ∑ i, (m i + (m i) ^ 2) ≤ 6 * ν * n := by
    calc ∑ i, (m i + (m i) ^ 2) ≤ ∑ _i : Fin n, (2 * ν + 4 * ν ^ 2) :=
        Finset.sum_le_sum fun i _ => add_le_add (hm1 i) (hm_sq i)
      _ = (2 * ν + 4 * ν ^ 2) * n := by simp; ring
      _ ≤ 6 * ν * n := by
        apply mul_le_mul_of_nonneg_right _ hn0.le
        nlinarith
  have hsum0 : 0 ≤ ∑ i, m i := Finset.sum_nonneg fun i _ => hm0 i
  have hsum1 : ∑ i, m i ≤ 2 * ν * n := by
    calc ∑ i, m i ≤ ∑ _i : Fin n, 2 * ν := Finset.sum_le_sum fun i _ => hm1 i
      _ = _ := by simp; ring
  have hsquare : (∑ i, m i) ^ 2 ≤ 4 * ν ^ 2 * n ^ 2 := by
    nlinarith
  have hlarge : ν * n ≤ ν ^ 2 * n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnν) (mul_nonneg hν0.le hn0.le)]
  nlinarith [sq_nonneg (ν * n)]

/-- A spectral upper bound implies the required second moment bound for actual photon counting. -/
theorem photon_second_moment_le_of_spectral_bound {n : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef) (hR1 : (1 - R).PosDef)
    (ν : ℝ) (hn : 1 ≤ n) (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1)
    (hupper : (((2 * ν / (1 + 2 * ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - R).PosSemidef) :
    ∑' u : Occupation (Fin n), ENNReal.ofReal ((∑ i, (u i : ℝ)) ^ 2) *
      ENNReal.ofReal (fugacityCoeff R u u).re ≤ ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  obtain ⟨U, d, hU1, hU2, hspec, hd0, hd1⟩ := spectral_data R hR hR1
  have hdu := diagonal_upper_bound R U d (2 * ν / (1 + 2 * ν)) hU1 hspec hupper
  have hm0 : ∀ i, 0 ≤ d i / (1 - d i) := fun i => div_nonneg (hd0 i) (by linarith [hd1 i])
  have hmu : ∀ i, d i / (1 - d i) ≤ 2 * ν := by
    intro i
    apply (div_le_iff₀ (by linarith [hd1 i])).mpr
    have h := (le_div_iff₀ (by positivity : 0 < 1 + 2 * ν)).mp (hdu i)
    nlinarith
  have hsum := hasSum_photon_second_moment R U d hR hU1 hU2 hspec hd0 hd1
  have hdet : (1 - R).det = ((∏ i, (1 - d i) : ℝ) : ℂ) := by
    rw [hspec, one_sub_conj U _ hU2, one_sub_diagonal, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal, mul_right_comm, ← Matrix.det_mul, hU2, Matrix.det_one, one_mul,
      Complex.ofReal_prod]
  have hx0 : ∀ u, 0 ≤ (fugacityCoeff R u u).re := by
    intro u
    unfold fugacityCoeff
    rw [Matrix.smul_apply, smul_eq_mul, hdet, Complex.re_ofReal_mul]
    exact mul_nonneg (Finset.prod_nonneg fun i _ => by linarith [hd1 i])
      (gammaFock_diag_real R hR u).2
  have htotal : (∑' u : Occupation (Fin n), ENNReal.ofReal ((∑ i, (u i : ℝ)) ^ 2) *
      ENNReal.ofReal (fugacityCoeff R u u).re) =
      ENNReal.ofReal ((∑ i, (d i / (1 - d i) + (d i / (1 - d i)) ^ 2)) +
        (∑ i, d i / (1 - d i)) ^ 2) := by
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
      (fun u => mul_nonneg (sq_nonneg _) (hx0 u)) hsum.summable]
    exact tsum_congr fun u => (ENNReal.ofReal_mul (sq_nonneg _)).symm
  rw [htotal]
  exact ENNReal.ofReal_le_ofReal (occupation_moment_bound ν hn hν hν1 _ hm0 hmu)

theorem opnorm_form {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) (c : ℝ)
    (h : WHMultiplicativity.schattenNorm ⊤ X ≤ c) :
    (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
      (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef := by
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ ≤ c := by
    simpa [WHMultiplicativity.schattenNorm] using h
  have key : ∀ v : Fin n → ℂ, |(star v ⬝ᵥ (X *ᵥ v)).re| ≤ c * ∑ i, ‖v i‖ ^ 2 := by
    intro v
    set w : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v with hw
    have h1 : inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w) = star v ⬝ᵥ (X *ᵥ v) := by
      rw [hw, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    have h2 : ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖ ≤ c * ‖w‖ ^ 2 := by
      calc ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖
          ≤ ‖w‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X w‖ := norm_inner_le_norm _ _
        _ ≤ ‖w‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖w‖ * (c * ‖w‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)
        _ = c * ‖w‖ ^ 2 := by ring
    have h3 : ‖w‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [h1, h3] at h2
    exact (Complex.abs_re_le_norm _).trans h2
  have hsq : ∀ v : Fin n → ℂ, star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have him : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).im = 0 := fun v =>
    hX.im_star_dotProduct_mulVec_self v
  have hc1 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.sub hX) fun v => ?_
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.2]
    · rw [Complex.sub_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, sub_zero]
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.add hX) fun v => ?_
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.1]
    · rw [Complex.add_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, add_zero]


/-- Fugacity matrices in the hard family have eigenvalues at most `2ν/(1+2ν)`. -/
theorem family_spectral_bounds {n : ℕ} (ν ξ : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    (fugacityFamily ν ξ X).PosSemidef ∧ (1 - fugacityFamily ν ξ X).PosDef ∧
    ((((2 * ν / (1 + 2 * ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) -
      fugacityFamily ν ξ X).PosSemidef := by
  have hXh : (X : Matrix (Fin n) (Fin n) ℂ).IsHermitian := X.2.1
  have hop : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ 4 := hX
  obtain ⟨hminus, hplus⟩ := opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) hXh 4 hop
  have h14 : 0 < 1 - 4 * ξ := by linarith
  have h14' : 1 - 4 * ξ ≠ 0 := h14.ne'
  have h1ν : 1 + ν ≠ 0 := by positivity
  set r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν)) with hr
  have hrpos : 0 < r := by positivity
  have hrt : r * (1 - 4 * ξ) = ν / (1 + ν) := by
    rw [hr]
    field_simp
  have hRdef : fugacityFamily ν ξ X =
      ((r : ℝ) : ℂ) • (1 + ((ξ : ℝ) : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) := rfl
  have e1 : fugacityFamily ν ξ X - ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef, ← hrt]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hRν : (fugacityFamily ν ξ X -
      ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [e1]
    exact hplus.smul (Complex.zero_le_real.mpr (by positivity))
  have hRpsd : (fugacityFamily ν ξ X).PosSemidef := by
    have e : fugacityFamily ν ξ X = (fugacityFamily ν ξ X -
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [sub_add_cancel]
    rw [e]
    exact hRν.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity)))
  let b : ℝ := 2 * ν / (1 + 2 * ν)
  have hb1 : b < 1 := by
    dsimp [b]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hr_bound : r * (1 + 4 * ξ) ≤ b := by
    rw [hr, div_mul_eq_mul_div]
    dsimp [b]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hξν : ξ * ν ≤ ξ := by nlinarith
    have hsmall : 0 ≤ 1 - 12 * ξ - 16 * ξ * ν := by nlinarith
    nlinarith [mul_nonneg hν0.le hsmall]
  have heq : (b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - fugacityFamily ν ξ X =
      ((b - r * (1 + 4 * ξ) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
          (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hu : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - fugacityFamily ν ξ X).PosSemidef := by
    rw [heq]
    exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hr_bound))).add
      (hminus.smul (Complex.zero_le_real.mpr (by positivity)))
  have hp : (1 - fugacityFamily ν ξ X).PosDef := by
    have he : 1 - fugacityFamily ν ξ X =
        ((1 - b : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
          ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - fugacityFamily ν ξ X) := by
      push_cast
      module
    rw [he]
    exact (Matrix.PosDef.one.smul (by exact_mod_cast (sub_pos.mpr hb1))).add_posSemidef hu
  exact ⟨hRpsd, hp, hu⟩

/-- Eq. (92): the actual total photon count in the hard family has second moment at most `12ν²n²`. -/
theorem fugacity_count_second_moment {n : ℕ} (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∑' u : Occupation (Fin n), ENNReal.ofReal ((∑ i, (u i : ℝ)) ^ 2) *
      ENNReal.ofReal (fugacityCoeff (fugacityFamily ν ξ X) u u).re ≤
        ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := (one_div_pos.mpr hn0).trans_le hν
  obtain ⟨hR, hR1, hu⟩ := family_spectral_bounds ν ξ hν0 hν1 hξ hξ32 X hX
  exact photon_second_moment_le_of_spectral_bound _ hR hR1 ν hn hν hν1 hu


/-- Regrouping nonnegative second-moment weights by a count statistic. -/
theorem count_second_moment_regroup {I : Type} (c : I → ℕ) (p : I → ℝ≥0∞) :
    (∑' k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2) *
      ∑' u : I, if c u = k then p u else 0) =
      ∑' u : I, ENNReal.ofReal ((c u : ℝ) ^ 2) * p u := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun u => ?_
  rw [tsum_eq_single (c u)]
  · simp
  · intro k hk
    simp [Ne.symm hk]

/-- Eq. (92) expressed using the distribution of the scalar total photon count. -/
theorem fugacity_count_distribution_second_moment {n : ℕ} (ν ξ : ℝ) (hn : 1 ≤ n)
    (hν : 1 / (n : ℝ) ≤ ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Gsupp n) :
    ∑' k : ℕ, ENNReal.ofReal ((k : ℝ) ^ 2) *
      (∑' u : Occupation (Fin n), if ∑ i, u i = k then
        ENNReal.ofReal (fugacityCoeff (fugacityFamily ν ξ X) u u).re else 0) ≤
          ENNReal.ofReal (12 * ν ^ 2 * n ^ 2) := by
  rw [count_second_moment_regroup]
  simp only [Nat.cast_sum]
  exact fugacity_count_second_moment ν ξ hn hν hν1 hξ hξ32 X hX

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5PhiSupport -/
section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 800000

theorem matrix_entry_le_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have hi : ‖e i‖ = 1 := e.orthonormal.norm_eq_one i
  have hj : ‖e j‖ = 1 := e.orthonormal.norm_eq_one j
  have h := norm_inner_le_norm (𝕜 := ℂ) (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e j))
  have he : inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e j)) = A i j := by
    rw [EuclideanSpace.basisFun_inner]
    simp [e, EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]
  rw [he, hi, one_mul] at h
  have hb := (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm (e j)
  rw [hj, mul_one] at hb
  exact h.trans hb

theorem matrix_trace_le_operator_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.trace‖ ≤ n * ‖A‖ := by
  calc
    ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, ‖A‖ := Finset.sum_le_sum fun i _ => matrix_entry_le_operator_norm A i i
    _ = n * ‖A‖ := by simp

/-- The local relative parametrization stays in the prior support throughout
the full parameter range used by the hard family. Only support is asserted;
the derivative/Jacobian claims of Lemma 8 are not needed here. -/
theorem PhiMap_mem_Gsupp {n : ℕ} (hn : 1 ≤ n) (X : Herm0 n) (hX : X ∈ Ggood n)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (Z : Herm0 n) (hZ : Z ∈ herm0Ball ⊤ 0 (1 / 10)) :
    PhiMap X ξ Z ∈ Gsupp n := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  letI : NeZero n := ⟨by omega⟩
  have hXnorm : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 := hX
  have hZnorm : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10 := by
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10
    simpa [herm0Ball, WHMultiplicativity.schattenNorm] using hZ
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
  let d : ℂ := 1 + (ξ : ℂ) ^ 2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  let T : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt S * (Z : Matrix (Fin n) (Fin n) ℂ) * CFC.sqrt S
  let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  have hSp : S.PosSemidef := by
    have hx := (opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) X.property.1 3 hX).2
    have he : S = ((1 - 3 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (ξ : ℂ) • ((3 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X) := by
      dsimp [S]
      push_cast
      module
    rw [he]
    exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith))).add
      (hx.smul (Complex.zero_le_real.mpr hξ.le))
  have hsqrt : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hSp.nonneg
  have hSnorm : ‖S‖ ≤ 1 + 3 * ξ := by
    calc ‖S‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖(ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)‖ := norm_add_le _ _
      _ = 1 + ξ * ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ := by
        rw [norm_one, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
      _ ≤ 1 + 3 * ξ := by nlinarith only [hXnorm, hξ]
  have hTnorm : ‖T‖ ≤ (1 + 3 * ξ) / 10 := by
    calc ‖T‖ ≤ ‖CFC.sqrt S‖ * ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ * ‖CFC.sqrt S‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖CFC.sqrt S‖ * (1 / 10) * ‖CFC.sqrt S‖ := by gcongr
      _ = ‖S‖ / 10 := by rw [CFC.norm_sqrt S hSp.nonneg]; nlinarith [Real.sq_sqrt (norm_nonneg S)]
      _ ≤ (1 + 3 * ξ) / 10 := by linarith
  have htr : ‖((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace‖ ≤ n * (3 / 10) := by
    refine (matrix_trace_le_operator_norm _).trans ?_
    have hm := norm_mul_le (X : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin n) (Fin n) ℂ)
    have hab : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ * ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 * (1 / 10) := by gcongr
    nlinarith only [hm, hab, hn0]
  have henorm : ‖e‖ ≤ 3 * ξ / 10 := by
    dsimp [e]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ,
      Complex.norm_natCast]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [htr, hξ, hn0]
  have hdform : d = 1 + (ξ : ℂ) * e := by dsimp [d, e]; ring
  have hdnorm : 1 - 3 * ξ ^ 2 / 10 ≤ ‖d‖ := by
    have heq : 1 - d = -(ξ : ℂ) * e := by rw [hdform]; ring
    have hrev := norm_sub_norm_le (1 : ℂ) d
    rw [norm_one, heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ] at hrev
    nlinarith only [hrev, henorm, hξ]
  have hdpos : 0 < ‖d‖ := by nlinarith only [hdnorm, hξ, hξ32]
  have hd0 : d ≠ 0 := norm_pos_iff.mp hdpos
  have hnum : ‖(X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 4 * ‖d‖ := by
    have hnorm : ‖(X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤
        ‖(X : Matrix (Fin n) (Fin n) ℂ) + T‖ + ‖e • (1 : Matrix (Fin n) (Fin n) ℂ)‖ := norm_sub_le _ _
    have hsum : ‖(X : Matrix (Fin n) (Fin n) ℂ) + T‖ ≤
        ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ + ‖T‖ := norm_add_le _ _
    rw [norm_smul, norm_one, mul_one] at hnorm
    nlinarith only [hnorm, hsum, hXnorm, hTnorm, henorm, hdnorm, hξ, hξ32]
  have hformula : (ξ⁻¹ : ℂ) •
      (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1) =
      d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    have hprod : CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S = S + (ξ : ℂ) • T := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
        hsqrt, T]
    rw [hprod]
    ext i j
    simp only [S, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    rw [hdform]
    push_cast
    have hden : 1 + (ξ : ℂ) * e ≠ 0 := by simpa only [hdform] using hd0
    have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
    field_simp [hden, hξc]
    <;> ring
  unfold PhiMap
  dsimp only
  split_ifs with h
  · change ‖(ξ⁻¹ : ℂ) •
        (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1)‖ ≤ 4
    rw [hformula, norm_smul, norm_inv, mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hdpos).mpr hnum
  · simp [Gsupp, WHMultiplicativity.schattenNorm]

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5PhiMeasurable -/
section
open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace BosonicLearn.Prop5

/-- The totalized relative-perturbation map is Borel measurable. The
matrix square root is constant because the base point is fixed. -/
theorem measurable_PhiMap {n : ℕ} (X₀ : Herm0 n) (ξ : ℝ) :
    Measurable (PhiMap X₀ ξ) := by
  classical
  letI : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X₀ : Matrix (Fin n) (Fin n) ℂ)
  let M : Herm0 n → Matrix (Fin n) (Fin n) ℂ := fun Z =>
    (ξ⁻¹ : ℂ) • (((1 + (ξ : ℂ) ^ 2 *
      ((X₀ : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n)⁻¹) •
      (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1)
  have hM : Measurable M := by
    dsimp [M]
    fun_prop
  have hs : MeasurableSet {Z : Herm0 n | M Z ∈ Herm0 n} :=
    (Herm0_isClosed n).measurableSet.preimage hM
  have hf : Measurable (fun Z : {Z : Herm0 n | M Z ∈ Herm0 n} =>
      (⟨M Z, Z.property⟩ : Herm0 n)) := by
    change @Measurable _ _ _ (borel _) _
    rw [borel_comap]
    exact (hM.comp measurable_subtype_coe).subtype_mk
  unfold PhiMap
  change Measurable (fun Z => if h : M Z ∈ Herm0 n then (⟨M Z, h⟩ : Herm0 n) else 0)
  exact hf.dite (measurable_const : Measurable
    (fun _ : ({Z : Herm0 n | M Z ∈ Herm0 n}ᶜ : Set (Herm0 n)) => (0 : Herm0 n))) hs

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5FamilyEntries -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix BigOperators

namespace BosonicLearn.Prop5
noncomputable section

theorem continuous_fugacityCoeff_entry_family_entries {n : ℕ} (u v : Occupation (Fin n)) :
    Continuous (fun R : Matrix (Fin n) (Fin n) ℂ => fugacityCoeff R u v) := by
  classical
  unfold fugacityCoeff gammaFock
  fun_prop

theorem continuous_family_entry_family_entries {n : ℕ} (ν ξ : ℝ) (u v : Occupation (Fin n)) :
    Continuous (fun X : Herm0 n => fugacityCoeff (fugacityFamily ν ξ X) u v) := by
  apply (continuous_fugacityCoeff_entry_family_entries u v).comp
  unfold fugacityFamily
  fun_prop

theorem isCompact_Gsupp (n : ℕ) : IsCompact (Gsupp n) := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  apply Metric.isCompact_of_isClosed_isBounded
  · simpa [Gsupp, WHMultiplicativity.schattenNorm] using isClosed_le hc continuous_const
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨4, ?_⟩
    intro X hX
    change ‖fun i j => (X : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ 4
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro j
    exact (matrix_entry_le_operator_norm (X : Matrix (Fin n) (Fin n) ℂ) i j).trans hX

theorem finite_cond_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Set Ω) : IsFiniteMeasure (cond μ s) := by
  constructor
  calc
    (cond μ s) Set.univ = (μ s)⁻¹ * μ s := by
      simp [ProbabilityTheory.cond, Measure.smul_apply]
    _ ≤ 1 := ENNReal.inv_mul_le_one _
    _ < ⊤ := by norm_num

theorem measurableSet_operator_ball (n : ℕ) (b : ℝ) :
    MeasurableSet (herm0Ball ⊤ (0 : Herm0 n) b) := by
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  simpa [herm0Ball, WHMultiplicativity.schattenNorm] using
    measurableSet_le hc.measurable measurable_const

/-- Every finite tensor entry of the perturbed fugacity family is integrable under
the uniform perturbation measure. Polynomial continuity and compact prior support
give a bound, so no differentiability or explicit entry estimate is required. -/
theorem integrable_family_Phi_product_entry {ι : Type*} [Fintype ι]
    (n : ℕ) (hn : 1 ≤ n) (ν ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X₀ : Herm0 n) (hX₀ : X₀ ∈ Ggood n) (b : ℝ) (hb10 : b ≤ 1 / 10)
    (u v : ι → Occupation (Fin n)) :
    Integrable (fun Z => ∏ t, fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) (u t) (v t))
      (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
  have := finite_cond_measure (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  let f := fun X : Herm0 n => ∏ t, fugacityCoeff (fugacityFamily ν ξ X) (u t) (v t)
  have hf : Continuous f := continuous_finsetProd _ fun t _ => continuous_family_entry_family_entries ν ξ (u t) (v t)
  obtain ⟨C, hC⟩ := (isCompact_Gsupp n).exists_bound_of_continuousOn hf.continuousOn
  apply Integrable.of_bound ((hf.measurable.comp (measurable_PhiMap X₀ ξ)).aestronglyMeasurable) C
  apply ae_cond_of_forall_mem (measurableSet_operator_ball n b)
  intro Z hZ
  apply hC
  apply PhiMap_mem_Gsupp hn X₀ hX₀ ξ hξ hξ32 Z
  exact le_trans hZ hb10

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop2Averaging -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

/-- Conditioning a centrally symmetric measure on a symmetric set preserves symmetry. -/
theorem map_neg_cond {E : Type*} [MeasurableSpace E] [InvolutiveNeg E] [MeasurableNeg E]
    (μ : Measure E) [μ.IsNegInvariant] (s : Set E) (hs : Neg.neg ⁻¹' s = s) :
    (cond μ s).map Neg.neg = cond μ s := by
  have hm := measurableEmbedding_neg.restrict_map μ s
  rw [Measure.map_neg_eq_self μ, hs] at hm
  rw [ProbabilityTheory.cond, Measure.map_smul, ← hm]

/-- An odd function has zero integral against a centrally symmetric measure. -/
theorem integral_odd_eq_zero {E : Type*} [MeasurableSpace E] [InvolutiveNeg E] [MeasurableNeg E]
    (μ : Measure E) (hμ : μ.map Neg.neg = μ) (f : E → ℝ) (hf : ∀ x, f (-x) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  have h := measurableEmbedding_neg.integral_map (μ := μ) f
  rw [hμ] at h
  simp only [hf, integral_neg] at h
  linarith

/-- The scalar denominator in the relative parametrization. -/
def relativeNormalizer {n : ℕ} (X : Herm0 n) (ξ : ℝ) (Z : Herm0 n) : ℝ :=
  1 + ξ ^ 2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace.re / n

theorem continuous_relativeNormalizer {n : ℕ} (X : Herm0 n) (ξ : ℝ) :
    Continuous (relativeNormalizer X ξ) := by
  unfold relativeNormalizer
  fun_prop

theorem relativeNormalizer_pos {n : ℕ} (hn : 1 ≤ n) (X : Herm0 n) (hX : X ∈ Ggood n)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32) (Z : Herm0 n) (hZ : Z ∈ Gsupp n) :
    1 / 2 ≤ relativeNormalizer X ξ Z := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : |((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace.re| ≤ 12 * n := by
    calc
      _ ≤ ‖((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace‖ := Complex.abs_re_le_norm _
      _ ≤ n * ‖(X : Matrix (Fin n) (Fin n) ℂ) * Z‖ := Prop5.matrix_trace_le_operator_norm _
      _ ≤ n * (‖(X : Matrix (Fin n) (Fin n) ℂ)‖ * ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖) := by
        gcongr
        exact norm_mul_le _ _
      _ ≤ n * (3 * 4) := by
        gcongr
        · exact hX
        · exact hZ
      _ = _ := by ring
  have hg : |ξ ^ 2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace.re / n| ≤ 12 * ξ ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg ξ), abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg ξ)]
  have hgl := (abs_le.mp hg).1
  unfold relativeNormalizer
  nlinarith

theorem neg_preimage_operator_ball (n : ℕ) (b : ℝ) :
    Neg.neg ⁻¹' herm0Ball (n := n) ⊤ 0 b = herm0Ball ⊤ 0 b := by
  ext Z
  simp [herm0Ball, WHMultiplicativity.schattenNorm, map_neg]

/-- Continuous functions on the compact support are integrable on a smaller uniform ball. -/
theorem integrable_cond_operator_ball_of_continuousOn (n : ℕ) (b : ℝ) (hb : b ≤ 4)
    (f : Herm0 n → ℝ) (hm : Measurable f) (hf : ContinuousOn f (Gsupp n)) :
    Integrable f (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
  have := Prop5.finite_cond_measure (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  obtain ⟨C, hC⟩ := (Prop5.isCompact_Gsupp n).exists_bound_of_continuousOn hf
  apply Integrable.of_bound hm.aestronglyMeasurable C
  apply ae_cond_of_forall_mem (Prop5.measurableSet_operator_ball n b)
  intro Z hZ
  have hZ' : WHMultiplicativity.schattenNorm ⊤ (Z : Matrix (Fin n) (Fin n) ℂ) ≤ b := by
    simpa [herm0Ball] using hZ
  exact hC Z (le_trans hZ' hb)

/-- The trace-linear term in the relative normalizer has zero average by symmetry. -/
theorem integral_relativeNormalizer_sub_one {n : ℕ} (X : Herm0 n) (ξ b : ℝ) :
    ∫ Z, (relativeNormalizer X ξ Z - 1)
      ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) = 0 := by
  apply integral_odd_eq_zero _
    (map_neg_cond _ _ (neg_preimage_operator_ball n b))
  intro Z
  simp [relativeNormalizer, Matrix.mul_neg, Matrix.trace_neg]
  ring

/-- Equation (69): the relative scalar normalizer costs nothing on average. -/
theorem integral_log_relativeNormalizer_nonpos {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (b : ℝ) (hb : b ≤ 4) :
    ∫ Z, Real.log (relativeNormalizer X ξ Z)
      ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) ≤ 0 := by
  have hcont := continuous_relativeNormalizer X ξ
  have hlog : ContinuousOn (fun Z => Real.log (relativeNormalizer X ξ Z)) (Gsupp n) :=
    hcont.continuousOn.log (fun Z hZ => ne_of_gt (by
      have := relativeNormalizer_pos hn X hX ξ hξ hξ32 Z hZ
      linarith))
  have hi := integrable_cond_operator_ball_of_continuousOn n b hb _
    (Real.measurable_log.comp hcont.measurable) hlog
  have hj := integrable_cond_operator_ball_of_continuousOn n b hb
    (fun Z => relativeNormalizer X ξ Z - 1)
    (hcont.sub continuous_const).measurable (hcont.sub continuous_const).continuousOn
  rw [← integral_relativeNormalizer_sub_one X ξ b]
  apply integral_mono_ae hi hj
  apply ae_cond_of_forall_mem (Prop5.measurableSet_operator_ball n b)
  intro Z hZ
  have hZ' : WHMultiplicativity.schattenNorm ⊤ (Z : Matrix (Fin n) (Fin n) ℂ) ≤ b := by
    simpa [herm0Ball] using hZ
  exact Real.log_le_sub_one_of_pos (by
    have := relativeNormalizer_pos hn X hX ξ hξ hξ32 Z (le_trans hZ' hb)
    linarith)

/-- Jensen's inequality turns per-copy expected log bounds into the full
fixed-transcript product bound. -/
theorem product_expectation_lower_of_log_bounds {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : I → Ω → ℝ) (c : I → ℝ)
    (hfpos : ∀ i, ∀ᵐ x ∂μ, 0 < f i x)
    (hlog : ∀ i, Integrable (fun x => Real.log (f i x)) μ)
    (hprod : Integrable (fun x => ∏ i, f i x) μ)
    (hlower : ∀ i, -c i ≤ ∫ x, Real.log (f i x) ∂μ) :
    ENNReal.ofReal (Real.exp (-(∑ i, c i))) ≤
      ∫⁻ x, ENNReal.ofReal (∏ i, f i x) ∂μ := by
  classical
  have hpos : ∀ᵐ x ∂μ, ∀ i, 0 < f i x := (ae_all_iff).mpr hfpos
  have hi : Integrable (fun x => ∑ i, Real.log (f i x)) μ :=
    integrable_finsetSum _ fun i _ => hlog i
  have heq : (fun x => Real.exp (∑ i, Real.log (f i x))) =ᵐ[μ] (fun x => ∏ i, f i x) := by
    filter_upwards [hpos] with x hx
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => Real.exp_log (hx i)
  have hexp := hprod.congr heq.symm
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hi hexp
  have hl : -(∑ i, c i) ≤ ∫ x, ∑ i, Real.log (f i x) ∂μ := by
    rw [integral_finsetSum _ (fun i _ => hlog i), ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hlower i
  calc
    _ ≤ ENNReal.ofReal (∫ x, Real.exp (∑ i, Real.log (f i x)) ∂μ) :=
      ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.mpr hl).trans hj)
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (∑ i, Real.log (f i x))) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hexp
        (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
    _ = _ := lintegral_congr_ae (heq.fun_comp ENNReal.ofReal)

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop5SectorCore -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn.Prop5

/-- Finite sums of lower integrals are bounded by the lower integral
of the sum, even without measurability assumptions. -/
theorem finset_lintegral_le_lintegral_sum
    {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset I) (f : I → Ω → ℝ≥0∞) :
    (∑ i ∈ s, ∫⁻ x, f i x ∂μ) ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- A common likelihood lower bound survives finite nonnegative
mixtures. Cross multiplication avoids zero-denominator edge cases;
lower-integral superadditivity avoids measurable eigenvector choices. -/
theorem finite_mixture_likelihood_bound
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (w b : I → ℝ≥0∞) (f : I → Ω → ℝ≥0∞)
    (ell : ℝ≥0∞) (h : ∀ i, ell * b i ≤ ∫⁻ x, f i x ∂μ) :
    ell * (∑ i, w i * b i) ≤ ∫⁻ x, ∑ i, w i * f i x ∂μ := by
  classical
  calc
    ell * (∑ i, w i * b i) = ∑ i, w i * (ell * b i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    _ ≤ ∑ i, w i * (∫⁻ x, f i x ∂μ) := by
      gcongr with i
      exact h i
    _ ≤ ∑ i, ∫⁻ x, w i * f i x ∂μ :=
      Finset.sum_le_sum fun i _ => lintegral_const_mul_le (w i) (f i)
    _ ≤ ∫⁻ x, ∑ i, w i * f i x ∂μ :=
      finset_lintegral_le_lintegral_sum μ Finset.univ _

/-- Divide a cross-multiplied likelihood bound by a finite positive
baseline. No measurability of the perturbed likelihood is required. -/
theorem likelihood_ratio_bound_of_cross_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (ell b : ℝ≥0∞) (hb0 : b ≠ 0) (hbfin : b ≠ ⊤)
    (h : ell * b ≤ ∫⁻ x, f x ∂μ) :
    ell ≤ ∫⁻ x, f x / b ∂μ := by
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const' b⁻¹ f (ENNReal.inv_ne_top.mpr hb0)]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbfin)).mpr h

theorem likelihood_cross_bound_of_ratio_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (ell b : ℝ≥0∞) (hb0 : b ≠ 0) (hbfin : b ≠ ⊤)
    (h : ell ≤ ∫⁻ x, f x / b ∂μ) :
    ell * b ≤ ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv] at h
  rw [lintegral_mul_const' b⁻¹ f (ENNReal.inv_ne_top.mpr hb0)] at h
  exact (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbfin)).mp h

/-- Expand a product of finite mixtures into its choice tuples and
apply the same fixed-sector bound to every tuple. This is the algebraic
step extending rank-one product effects to arbitrary positive effects. -/
theorem product_mixture_likelihood_bound
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    {I : J → Type*} [∀ j, Fintype (I j)]
    (μ : Measure Ω) (w b : ∀ j, I j → ℝ≥0∞)
    (f : ∀ j, I j → Ω → ℝ≥0∞) (ell : ℝ≥0∞)
    (h : ∀ choice : ∀ j, I j,
      ell * (∏ j, b j (choice j)) ≤ ∫⁻ x, ∏ j, f j (choice j) x ∂μ) :
    ell * (∏ j, ∑ i, w j i * b j i) ≤
      ∫⁻ x, ∏ j, ∑ i, w j i * f j i x ∂μ := by
  classical
  have hm := finite_mixture_likelihood_bound μ
    (fun choice : ∀ j, I j => ∏ j, w j (choice j))
    (fun choice : ∀ j, I j => ∏ j, b j (choice j))
    (fun choice x => ∏ j, f j (choice j) x) ell h
  have hb : (∑ choice : ∀ j, I j, (∏ j, w j (choice j)) * (∏ j, b j (choice j))) =
      ∏ j, ∑ i, w j i * b j i := by
    simp only [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun j i => w j i * b j i)).symm
  have hf (x : Ω) :
      (∑ choice : ∀ j, I j, (∏ j, w j (choice j)) * (∏ j, f j (choice j) x)) =
        ∏ j, ∑ i, w j i * f j i x := by
    simp only [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun j i => w j i * f j i x)).symm
  simpa only [hb, hf] using hm

/-- Occupation vectors in a fixed total-photon-number sector. -/
abbrev PhotonSector (n k : ℕ) := {u : Occupation (Fin n) // ∑ i, u i = k}

private def sectorFinset (n k : ℕ) : Finset (Occupation (Fin n)) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (k + 1)).filter (fun u => ∑ i, u i = k)

private theorem mem_sectorFinset (n k : ℕ) (u : Occupation (Fin n)) :
    u ∈ sectorFinset n k ↔ ∑ i, u i = k := by
  classical
  unfold sectorFinset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  rw [Finset.mem_range, ← h]
  have hle : u i ≤ ∑ j, u j :=
    Finset.single_le_sum (f := fun j => u j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

noncomputable instance photonSectorFintype (n k : ℕ) : Fintype (PhotonSector n k) :=
  Fintype.ofFinset (sectorFinset n k) (mem_sectorFinset n k)

/-- Extend a finite-sector vector by zero to the whole Fock basis. -/
noncomputable def extendSector {n k : ℕ} (v : PhotonSector n k → ℂ) : Occupation (Fin n) → ℂ :=
  fun u => if h : ∑ i, u i = k then v ⟨u, h⟩ else 0

theorem extendSector_apply {n k : ℕ} (v : PhotonSector n k → ℂ) (u : PhotonSector n k) :
    extendSector v u = v u := by simp [extendSector, u.property]

theorem extendSector_zero_off_sector {n k : ℕ} (v : PhotonSector n k → ℂ)
    (u : Occupation (Fin n)) (hu : ∑ i, u i ≠ k) : extendSector v u = 0 := by
  simp [extendSector, hu]

theorem extendSector_ne_zero {n k : ℕ} (v : PhotonSector n k → ℂ) (hv : v ≠ 0) :
    extendSector v ≠ 0 := by
  intro hzero
  apply hv
  funext u
  simpa only [extendSector_apply, Pi.zero_apply] using congrFun hzero u

/-- Pointwise spectral decomposition of a positive finite-dimensional
effect into nonnegative weighted rank-one effects. The eigenvectors
are nonzero, including for zero eigenvalues. No measurable dependence
on an external outcome is asserted or needed. -/
theorem positive_effect_rank_one_decomposition
    {I : Type*} [Fintype I] [DecidableEq I]
    (E : Matrix I I ℂ) (hE : E.PosSemidef) :
    ∃ (w : I → ℝ) (v : I → I → ℂ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, v i ≠ 0) ∧
      ∀ a b, E a b = ∑ i, (w i : ℂ) * v i a * star (v i b) := by
  let U : Matrix I I ℂ := hE.isHermitian.eigenvectorUnitary
  let w : I → ℝ := hE.isHermitian.eigenvalues
  have hU : Uᴴ * U = 1 := by
    exact Unitary.coe_star_mul_self hE.isHermitian.eigenvectorUnitary
  have hspec : E = U * Matrix.diagonal (fun i => (w i : ℂ)) * Uᴴ := by
    simpa [U, w, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hE.isHermitian.spectral_theorem
  refine ⟨w, fun i a => U a i, hE.eigenvalues_nonneg, ?_, ?_⟩
  · intro i hzero
    have hdiag := congrFun (congrFun hU i) i
    have hz (a : I) : U a i = 0 := congrFun hzero a
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hz] at hdiag
  · intro a b
    rw [hspec, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    ring

/-- Finite-sector quadratic form, in the ordering used by Proposition 2. -/
def finiteQuadraticForm {I : Type*} [Fintype I]
    (R : Matrix I I ℂ) (v : I → ℂ) : ℝ :=
  (∑ a, ∑ b, star (v a) * R a b * v b).re

/-- The finite matrix block of an occupation-indexed matrix on one
total-photon-number sector. -/
def sectorBlock {n : ℕ} (k : ℕ)
    (R : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) :
    Matrix (PhotonSector n k) (PhotonSector n k) ℂ := fun u v => R u v

/-- Quadratic forms of zero-extended sector vectors involve only a
finite sum, with no convergence assumption on the ambient array. -/
theorem occupation_quadratic_form_eq_sector {n k : ℕ}
    (R : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (v : PhotonSector n k → ℂ) :
    (∑' u, ∑' w, star (extendSector v u) * R u w * extendSector v w).re =
      finiteQuadraticForm (sectorBlock k R) v := by
  have hinner (u : Occupation (Fin n)) :
      (∑' w : PhotonSector n k, star (extendSector v u) * R u w * extendSector v w) =
        ∑' w, star (extendSector v u) * R u w * extendSector v w := by
    apply tsum_subtype_eq_of_support_subset
      (s := {w : Occupation (Fin n) | ∑ i, w i = k})
      (f := fun w => star (extendSector v u) * R u w * extendSector v w)
    intro w hw
    by_contra hnot
    have hz : extendSector v w = 0 := extendSector_zero_off_sector v w hnot
    simpa only [Function.mem_support, hz, mul_zero, ne_eq, not_true_eq_false] using hw
  have houter :
      (∑' u : PhotonSector n k, ∑' w, star (extendSector v u) * R u w * extendSector v w) =
        ∑' u, ∑' w, star (extendSector v u) * R u w * extendSector v w := by
    apply tsum_subtype_eq_of_support_subset
      (s := {u : Occupation (Fin n) | ∑ i, u i = k})
      (f := fun u => ∑' w, star (extendSector v u) * R u w * extendSector v w)
    intro u hu
    by_contra hnot
    have hz : extendSector v u = 0 := extendSector_zero_off_sector v u hnot
    simpa only [Function.mem_support, hz, star_zero, zero_mul, tsum_zero, ne_eq,
      not_true_eq_false] using hu
  rw [← houter, tsum_fintype]
  unfold finiteQuadraticForm
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [← hinner u, tsum_fintype]
  simp only [extendSector_apply, sectorBlock]

/-- Second quantization acts multiplicatively on each finite sector. -/
theorem sector_gammaFock_mul {n : ℕ} (k : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    sectorBlock k (gammaFock (A * B)) =
      sectorBlock k (gammaFock A) * sectorBlock k (gammaFock B) := by
  classical
  ext u v
  simp only [sectorBlock, Matrix.mul_apply, gammaFock_mul, u.property]
  exact Finset.sum_subtype (sectorFinset n k) (mem_sectorFinset n k) _

theorem sector_gammaFock_one {n : ℕ} (k : ℕ) :
    sectorBlock k (gammaFock (1 : Matrix (Fin n) (Fin n) ℂ)) = 1 := by
  classical
  ext u v
  simp only [sectorBlock, (gammaFock_basic (1 : Matrix (Fin n) (Fin n) ℂ) u v).2.2,
    Matrix.one_apply, Subtype.val_inj]

theorem sector_gammaFock_conjTranspose {n : ℕ} (k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    sectorBlock k (gammaFock Aᴴ) = (sectorBlock k (gammaFock A))ᴴ := by
  ext u v
  exact (gammaFock_basic A u v).2.1

open scoped MatrixOrder in
/-- Each sector of the second quantization of a positive matrix is
positive; this follows directly from multiplicativity and adjoints. -/
theorem sector_gammaFock_posSemidef {n : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef) :
    (sectorBlock k (gammaFock R)).PosSemidef := by
  obtain ⟨A, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  rw [Matrix.star_eq_conjTranspose, sector_gammaFock_mul, sector_gammaFock_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Strict positivity survives second quantization on every finite
sector. The inverse is the second quantization of the inverse matrix. -/
theorem sector_gammaFock_posDef {n : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosDef) :
    (sectorBlock k (gammaFock R)).PosDef := by
  classical
  apply (sector_gammaFock_posSemidef k R hR.posSemidef).posDef_iff_isUnit.mpr
  let A := sectorBlock k (gammaFock R)
  let B := sectorBlock k (gammaFock R⁻¹)
  have hAB : A * B = 1 := by
    rw [← sector_gammaFock_mul, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit), sector_gammaFock_one]
  have hBA : B * A = 1 := by
    rw [← sector_gammaFock_mul, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit), sector_gammaFock_one]
  exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩

/-- Every finite block of a faithful passive Gaussian state is
strictly positive. In particular a nonzero positive sector effect
has a strictly positive probability under this state. -/
theorem sector_fugacityCoeff_posDef {n : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ)
    (hR : R.PosDef) (hIR : (1 - R).PosDef) :
    (sectorBlock k (fugacityCoeff R)).PosDef := by
  have h : sectorBlock k (fugacityCoeff R) =
      (1 - R).det • sectorBlock k (gammaFock R) := rfl
  rw [h]
  exact (sector_gammaFock_posDef k R hR).smul hIR.det_pos

theorem sector_fugacityCoeff_posSemidef {n : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ)
    (hR : R.PosSemidef) (hIR : (1 - R).PosSemidef) :
    (sectorBlock k (fugacityCoeff R)).PosSemidef := by
  have h : sectorBlock k (fugacityCoeff R) =
      (1 - R).det • sectorBlock k (gammaFock R) := rfl
  rw [h]
  exact (sector_gammaFock_posSemidef k R hR).smul hIR.det_nonneg

/-- All fugacity matrices in the hard family are strictly positive,
with the same lower spectral bound `ν/(1+ν)` as the scalar family. -/
theorem family_posDef {n : ℕ} (ν ξ : ℝ) (hν : 0 < ν)
    (hξ : 0 ≤ ξ) (hξlt : ξ < 1 / 4) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    (fugacityFamily ν ξ X).PosDef := by
  have hplus := (opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) X.2.1 4 hX).2
  have h14 : 0 < 1 - 4 * ξ := by linarith
  have h1ν : 0 < 1 + ν := by linarith
  let r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν))
  have hr : 0 < r := div_pos hν (mul_pos h14 h1ν)
  have hrt : r * (1 - 4 * ξ) = ν / (1 + ν) := by
    dsimp [r]
    field_simp
  have he : fugacityFamily ν ξ X =
      ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
      ((r * ξ : ℝ) : ℂ) • ((4 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (X : Matrix (Fin n) (Fin n) ℂ)) := by
    change ((r : ℝ) : ℂ) • (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) = _
    rw [← hrt]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [he]
  exact (Matrix.PosDef.one.smul (by exact_mod_cast (div_pos hν h1ν))).add_posSemidef
    (hplus.smul (Complex.zero_le_real.mpr (mul_nonneg hr.le hξ)))

theorem family_sector_posDef {n : ℕ} (ν ξ : ℝ) (hν : 0 < ν) (hνhi : ν ≤ 1)
    (hξ : 0 < ξ) (hξhi : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Gsupp n) (k : ℕ) :
    (sectorBlock k (fugacityCoeff (fugacityFamily ν ξ X))).PosDef :=
  sector_fugacityCoeff_posDef k _ (family_posDef ν ξ hν hξ.le (by linarith) X hX)
    (family_spectral_bounds ν ξ hν hνhi hξ hξhi X hX).2.1

theorem finiteQuadraticForm_nonneg {I : Type*} [Fintype I]
    (R : Matrix I I ℂ) (hR : R.PosSemidef) (v : I → ℂ) :
    0 ≤ finiteQuadraticForm R v := by
  simpa [finiteQuadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Pi.star_apply, mul_assoc] using hR.re_dotProduct_nonneg v

theorem finiteQuadraticForm_pos {I : Type*} [Fintype I]
    (R : Matrix I I ℂ) (hR : R.PosDef) (v : I → ℂ) (hv : v ≠ 0) :
    0 < finiteQuadraticForm R v := by
  simpa [finiteQuadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Pi.star_apply, mul_assoc] using hR.re_dotProduct_pos hv

/-- The Born pairing of a finite effect is the corresponding weighted
sum of its rank-one quadratic forms. -/
theorem effect_pairing_of_rank_one_decomposition
    {I J : Type*} [Fintype I] [Fintype J]
    (E R : Matrix I I ℂ) (w : J → ℝ) (v : J → I → ℂ)
    (hE : ∀ a b, E a b = ∑ j, (w j : ℂ) * v j a * star (v j b)) :
    (E * R).trace.re = ∑ j, w j * finiteQuadraticForm R (v j) := by
  have hc : (E * R).trace =
      ∑ j, (w j : ℂ) * ∑ a, ∑ b, star (v j a) * R a b * v j b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hE, Finset.sum_mul]
    calc
      (∑ a, ∑ b, ∑ j, (w j : ℂ) * v j a * star (v j b) * R b a) =
          ∑ j, ∑ a, ∑ b, (w j : ℂ) * v j a * star (v j b) * R b a := by
        conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
      _ = ∑ j, (w j : ℂ) * ∑ a, ∑ b, star (v j a) * R a b * v j b := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
  rw [hc]
  simp [finiteQuadraticForm, Complex.mul_re]

/-- A nonzero positive effect has strictly positive probability against
a positive-definite state on the finite sector. -/
theorem positive_effect_pairing_pos {I : Type*} [Fintype I] [DecidableEq I]
    (E R : Matrix I I ℂ) (hE : E.PosSemidef) (hEne : E ≠ 0) (hR : R.PosDef) :
    0 < (E * R).trace.re := by
  obtain ⟨w, v, hw, hv, hdec⟩ := positive_effect_rank_one_decomposition E hE
  rw [effect_pairing_of_rank_one_decomposition E R w v hdec]
  have hweight : ∃ i, 0 < w i := by
    by_contra h
    have hwzero (i : I) : w i = 0 := le_antisymm (not_lt.mp (not_exists.mp h i)) (hw i)
    apply hEne
    ext a b
    rw [hdec]
    simp [hwzero]
  obtain ⟨i, hi⟩ := hweight
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j)
    (finiteQuadraticForm_pos R hR (v j) (hv j)).le)
    ⟨i, Finset.mem_univ i, mul_pos hi (finiteQuadraticForm_pos R hR (v i) (hv i))⟩

theorem positive_effect_pairing_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (E R : Matrix I I ℂ) (hE : E.PosSemidef) (hR : R.PosSemidef) :
    0 ≤ (E * R).trace.re := by
  obtain ⟨w, v, hw, _, hdec⟩ := positive_effect_rank_one_decomposition E hE
  rw [effect_pairing_of_rank_one_decomposition E R w v hdec]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (finiteQuadraticForm_nonneg R hR (v i))

theorem ofReal_effect_pairing_decomposition
    {I J : Type*} [Fintype I] [Fintype J]
    (E R : Matrix I I ℂ) (hR : R.PosSemidef) (w : J → ℝ) (v : J → I → ℂ)
    (hw : ∀ j, 0 ≤ w j)
    (hdec : ∀ a b, E a b = ∑ j, (w j : ℂ) * v j a * star (v j b)) :
    ENNReal.ofReal (E * R).trace.re =
      ∑ j, ENNReal.ofReal (w j) * ENNReal.ofReal (finiteQuadraticForm R (v j)) := by
  rw [effect_pairing_of_rank_one_decomposition E R w v hdec,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hw j)
      (finiteQuadraticForm_nonneg R hR (v j)))]
  exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_mul (hw j)

theorem ofReal_product_ratio {J : Type*} [Fintype J]
    (a b : J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 < b j) :
    ENNReal.ofReal (∏ j, a j / b j) =
      (∏ j, ENNReal.ofReal (a j)) / (∏ j, ENNReal.ofReal (b j)) := by
  rw [Finset.prod_div_distrib,
    ENNReal.ofReal_div_of_pos (Finset.prod_pos fun j _ => hb j),
    ENNReal.ofReal_prod_of_nonneg (fun j _ => ha j),
    ENNReal.ofReal_prod_of_nonneg (fun j _ => (hb j).le)]

/-- The cross-multiplied form needs neither faithful states nor
nonzero effects, and is the form used to compare transcript measures. -/
theorem product_positive_effect_cross_bound
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (μ : Measure Ω) (R₀ E : ∀ j, Matrix (I j) (I j) ℂ)
    (R : ∀ j, Ω → Matrix (I j) (I j) ℂ)
    (hR₀ : ∀ j, (R₀ j).PosSemidef) (hE : ∀ j, (E j).PosSemidef)
    (hR : ∀ᵐ x ∂μ, ∀ j, (R j x).PosSemidef)
    (ell : ℝ≥0∞)
    (hvector : ∀ v : ∀ j, I j → ℂ, (∀ j, v j ≠ 0) →
      ell * (∏ j, ENNReal.ofReal (finiteQuadraticForm (R₀ j) (v j))) ≤
        ∫⁻ x, ∏ j, ENNReal.ofReal (finiteQuadraticForm (R j x) (v j)) ∂μ) :
    ell * (∏ j, ENNReal.ofReal (E j * R₀ j).trace.re) ≤
      ∫⁻ x, ∏ j, ENNReal.ofReal (E j * R j x).trace.re ∂μ := by
  classical
  choose w v hw hv hdec using fun j => positive_effect_rank_one_decomposition (E j) (hE j)
  have h := product_mixture_likelihood_bound μ
    (fun j i => ENNReal.ofReal (w j i))
    (fun j i => ENNReal.ofReal (finiteQuadraticForm (R₀ j) (v j i)))
    (fun j i x => ENNReal.ofReal (finiteQuadraticForm (R j x) (v j i))) ell
    (fun choice => hvector (fun j => v j (choice j)) (fun j => hv j (choice j)))
  have hbase : (∏ j, ∑ i, ENNReal.ofReal (w j i) *
      ENNReal.ofReal (finiteQuadraticForm (R₀ j) (v j i))) =
      ∏ j, ENNReal.ofReal (E j * R₀ j).trace.re := by
    apply Finset.prod_congr rfl
    intro j _
    exact (ofReal_effect_pairing_decomposition (E j) (R₀ j) (hR₀ j)
      (w j) (v j) (hw j) (hdec j)).symm
  have hpert : (fun x => ∏ j, ∑ i, ENNReal.ofReal (w j i) *
      ENNReal.ofReal (finiteQuadraticForm (R j x) (v j i))) =ᵐ[μ]
      (fun x => ∏ j, ENNReal.ofReal (E j * R j x).trace.re) := by
    filter_upwards [hR] with x hx
    apply Finset.prod_congr rfl
    intro j _
    exact (ofReal_effect_pairing_decomposition (E j) (R j x) (hx j)
      (w j) (v j) (hw j) (hdec j)).symm
  rwa [hbase, lintegral_congr_ae hpert] at h

/-- A product-vector likelihood bound extends to a product of arbitrary
nonzero positive effects on finite sectors. Spectral decompositions are
chosen separately for this fixed transcript, with no measurability
requirement on those choices. The perturbed states need only be positive
almost everywhere under the perturbation measure. -/
theorem product_positive_effect_likelihood_bound
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (μ : Measure Ω) (R₀ E : ∀ j, Matrix (I j) (I j) ℂ)
    (R : ∀ j, Ω → Matrix (I j) (I j) ℂ)
    (hR₀ : ∀ j, (R₀ j).PosDef) (hE : ∀ j, (E j).PosSemidef)
    (hEne : ∀ j, E j ≠ 0)
    (hR : ∀ᵐ x ∂μ, ∀ j, (R j x).PosSemidef)
    (ell : ℝ≥0∞)
    (hvector : ∀ v : ∀ j, I j → ℂ, (∀ j, v j ≠ 0) →
      ell ≤ ∫⁻ x, ENNReal.ofReal (∏ j,
        finiteQuadraticForm (R j x) (v j) / finiteQuadraticForm (R₀ j) (v j)) ∂μ) :
    ell ≤ ∫⁻ x, ENNReal.ofReal (∏ j,
      (E j * R j x).trace.re / (E j * R₀ j).trace.re) ∂μ := by
  classical
  choose w v hw hv hdec using fun j => positive_effect_rank_one_decomposition (E j) (hE j)
  let w' : ∀ j, I j → ℝ≥0∞ := fun j i => ENNReal.ofReal (w j i)
  let b : ∀ j, I j → ℝ≥0∞ := fun j i =>
    ENNReal.ofReal (finiteQuadraticForm (R₀ j) (v j i))
  let f : ∀ j, I j → Ω → ℝ≥0∞ := fun j i x =>
    ENNReal.ofReal (finiteQuadraticForm (R j x) (v j i))
  have hbase (j : J) (i : I j) : 0 < finiteQuadraticForm (R₀ j) (v j i) :=
    finiteQuadraticForm_pos (R₀ j) (hR₀ j) (v j i) (hv j i)
  have hchoice (choice : ∀ j, I j) :
      ell * (∏ j, b j (choice j)) ≤ ∫⁻ x, ∏ j, f j (choice j) x ∂μ := by
    have hbprod : (∏ j, b j (choice j)) =
        ENNReal.ofReal (∏ j, finiteQuadraticForm (R₀ j) (v j (choice j))) := by
      symm
      exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (hbase j (choice j)).le)
    have hdenpos : 0 < ∏ j, finiteQuadraticForm (R₀ j) (v j (choice j)) :=
      Finset.prod_pos fun j _ => hbase j (choice j)
    apply likelihood_cross_bound_of_ratio_bound μ (fun x => ∏ j, f j (choice j) x) ell
      (∏ j, b j (choice j))
      (by rw [hbprod]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hdenpos))
      (by rw [hbprod]; exact ENNReal.ofReal_ne_top)
    have heq :
        (fun x => ENNReal.ofReal (∏ j,
          finiteQuadraticForm (R j x) (v j (choice j)) /
            finiteQuadraticForm (R₀ j) (v j (choice j)))) =ᵐ[μ]
        (fun x => (∏ j, f j (choice j) x) / (∏ j, b j (choice j))) := by
      filter_upwards [hR] with x hx
      exact ofReal_product_ratio _ _ (fun j =>
        finiteQuadraticForm_nonneg (R j x) (hx j) _) (fun j => hbase j (choice j))
    rw [← lintegral_congr_ae heq]
    exact hvector (fun j => v j (choice j)) (fun j => hv j (choice j))
  have hcross := product_mixture_likelihood_bound μ w' b f ell hchoice
  let B : ℝ≥0∞ := ∏ j, ∑ i, w' j i * b j i
  let F : Ω → ℝ≥0∞ := fun x => ∏ j, ∑ i, w' j i * f j i x
  have hB : B = ENNReal.ofReal (∏ j, (E j * R₀ j).trace.re) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ =>
      (positive_effect_pairing_pos (E j) (R₀ j) (hE j) (hEne j) (hR₀ j)).le)]
    apply Finset.prod_congr rfl
    intro j _
    exact (ofReal_effect_pairing_decomposition (E j) (R₀ j) (hR₀ j).posSemidef
      (w j) (v j) (hw j) (hdec j)).symm
  have hBpos : 0 < ∏ j, (E j * R₀ j).trace.re :=
    Finset.prod_pos fun j _ => positive_effect_pairing_pos (E j) (R₀ j) (hE j) (hEne j) (hR₀ j)
  have hratio : ell ≤ ∫⁻ x, F x / B ∂μ :=
    likelihood_ratio_bound_of_cross_bound μ F ell B
      (by rw [hB]; exact ne_of_gt (ENNReal.ofReal_pos.mpr hBpos))
      (by rw [hB]; exact ENNReal.ofReal_ne_top) hcross
  have heq : (fun x => ENNReal.ofReal (∏ j,
      (E j * R j x).trace.re / (E j * R₀ j).trace.re)) =ᵐ[μ] (fun x => F x / B) := by
    filter_upwards [hR] with x hx
    rw [ofReal_product_ratio _ _
      (fun j => positive_effect_pairing_nonneg (E j) (R j x) (hE j) (hx j))
      (fun j => positive_effect_pairing_pos (E j) (R₀ j) (hE j) (hEne j) (hR₀ j))]
    congr 1
    · apply Finset.prod_congr rfl
      intro j _
      exact ofReal_effect_pairing_decomposition (E j) (R j x) (hx j)
        (w j) (v j) (hw j) (hdec j)
    · symm
      apply Finset.prod_congr rfl
      intro j _
      exact (ofReal_effect_pairing_decomposition (E j) (R₀ j) (hR₀ j).posSemidef
        (w j) (v j) (hw j) (hdec j)).symm
  rwa [← lintegral_congr_ae heq] at hratio

/-- Direct connection to Proposition 2's formulation with infinite
occupation-indexed quadratic forms. A fixed-sector rank-one bound
extends to arbitrary nonzero positive effects in those sectors. -/
theorem occupation_rank_one_bound_to_sector_effects
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n N : ℕ) (k : Fin N → ℕ)
    (R₀ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (R : Ω → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (E : ∀ t, Matrix (PhotonSector n (k t)) (PhotonSector n (k t)) ℂ)
    (hR₀ : ∀ t, (sectorBlock (k t) R₀).PosDef)
    (hE : ∀ t, (E t).PosSemidef) (hEne : ∀ t, E t ≠ 0)
    (hR : ∀ᵐ x ∂μ, ∀ t, (sectorBlock (k t) (R x)).PosSemidef)
    (ell : ℝ≥0∞)
    (hsector : ∀ ϕ : Fin N → Occupation (Fin n) → ℂ,
      (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
      ell ≤ ∫⁻ x, ENNReal.ofReal (∏ t,
        (∑' u, ∑' w, star (ϕ t u) * R x u w * ϕ t w).re /
        (∑' u, ∑' w, star (ϕ t u) * R₀ u w * ϕ t w).re) ∂μ) :
    ell ≤ ∫⁻ x, ENNReal.ofReal (∏ t,
      (E t * sectorBlock (k t) (R x)).trace.re /
      (E t * sectorBlock (k t) R₀).trace.re) ∂μ := by
  apply product_positive_effect_likelihood_bound μ (fun t => sectorBlock (k t) R₀) E
    (fun t x => sectorBlock (k t) (R x)) hR₀ hE hEne hR ell
  intro v hv
  have h := hsector (fun t => extendSector (v t))
    (fun t u hu => extendSector_zero_off_sector (v t) u hu)
    (fun t => extendSector_ne_zero (v t) (hv t))
  simpa only [occupation_quadratic_form_eq_sector] using h

/-- The measure-comparison form of the sector-effect extension.
Zero effects are allowed: their baseline weight is zero, so the
cross-multiplied lower bound remains meaningful. -/
theorem occupation_rank_one_bound_to_sector_effects_cross
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n N : ℕ) (k : Fin N → ℕ)
    (R₀ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (R : Ω → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ)
    (E : ∀ t, Matrix (PhotonSector n (k t)) (PhotonSector n (k t)) ℂ)
    (hR₀ : ∀ t, (sectorBlock (k t) R₀).PosDef)
    (hE : ∀ t, (E t).PosSemidef)
    (hR : ∀ᵐ x ∂μ, ∀ t, (sectorBlock (k t) (R x)).PosSemidef)
    (ell : ℝ≥0∞)
    (hsector : ∀ ϕ : Fin N → Occupation (Fin n) → ℂ,
      (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
      ell ≤ ∫⁻ x, ENNReal.ofReal (∏ t,
        (∑' u, ∑' w, star (ϕ t u) * R x u w * ϕ t w).re /
        (∑' u, ∑' w, star (ϕ t u) * R₀ u w * ϕ t w).re) ∂μ) :
    ell * (∏ t, ENNReal.ofReal (E t * sectorBlock (k t) R₀).trace.re) ≤
      ∫⁻ x, ∏ t, ENNReal.ofReal (E t * sectorBlock (k t) (R x)).trace.re ∂μ := by
  apply product_positive_effect_cross_bound μ (fun t => sectorBlock (k t) R₀) E
    (fun t x => sectorBlock (k t) (R x)) (fun t => (hR₀ t).posSemidef) hE hR ell
  intro v hv
  have hbpos (t : Fin N) : 0 < finiteQuadraticForm (sectorBlock (k t) R₀) (v t) :=
    finiteQuadraticForm_pos _ (hR₀ t) _ (hv t)
  have hbne : (∏ t, ENNReal.ofReal (finiteQuadraticForm (sectorBlock (k t) R₀) (v t))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro t _
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hbpos t))
  have hbfin : (∏ t, ENNReal.ofReal (finiteQuadraticForm (sectorBlock (k t) R₀) (v t))) ≠ ∞ :=
    ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  apply likelihood_cross_bound_of_ratio_bound μ _ ell _ hbne hbfin
  have hs := hsector (fun t => extendSector (v t))
    (fun t u hu => extendSector_zero_off_sector (v t) u hu)
    (fun t => extendSector_ne_zero (v t) (hv t))
  simp only [occupation_quadratic_form_eq_sector] at hs
  have heq : (fun x => ENNReal.ofReal (∏ t,
      finiteQuadraticForm (sectorBlock (k t) (R x)) (v t) /
        finiteQuadraticForm (sectorBlock (k t) R₀) (v t))) =ᵐ[μ]
      (fun x => (∏ t, ENNReal.ofReal (finiteQuadraticForm (sectorBlock (k t) (R x)) (v t))) /
        (∏ t, ENNReal.ofReal (finiteQuadraticForm (sectorBlock (k t) R₀) (v t)))) := by
    filter_upwards [hR] with x hx
    exact ofReal_product_ratio _ _ (fun t => finiteQuadraticForm_nonneg _ (hx t) _) hbpos
  rwa [← lintegral_congr_ae heq]

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop2SecondQuantization -/
section
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder

namespace BosonicLearn.Prop2
noncomputable section

/-- Second quantization is homogeneous of degree equal to the photon number
on each finite sector. -/
theorem gammaFock_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (u v : Occupation (Fin n)) :
    gammaFock (c • A) u v = c ^ (∑ i, u i) * gammaFock A u v := by
  classical
  unfold gammaFock
  rw [mul_left_comm (c ^ _)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M hM
  have hrow : ∀ i, ∑ j, M i j = u i := (Finset.mem_filter.mp hM).2.1
  simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, mul_div_assoc,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hrow]

theorem sector_gammaFock_smul {n : ℕ} (k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    Prop5.sectorBlock k (gammaFock (c • A)) = c ^ k • Prop5.sectorBlock k (gammaFock A) := by
  ext u v
  simp only [Prop5.sectorBlock, gammaFock_smul, u.property, Matrix.smul_apply, smul_eq_mul]

/-- A congruence before second quantization becomes a congruence in each photon sector. -/
theorem sector_gammaFock_congruence {n : ℕ} (k : ℕ)
    (S A : Matrix (Fin n) (Fin n) ℂ) :
    Prop5.sectorBlock k (gammaFock (Sᴴ * A * S)) =
      (Prop5.sectorBlock k (gammaFock S))ᴴ * Prop5.sectorBlock k (gammaFock A) *
        Prop5.sectorBlock k (gammaFock S) := by
  rw [Prop5.sector_gammaFock_mul, Prop5.sector_gammaFock_mul,
    Prop5.sector_gammaFock_conjTranspose]

/-- Quadratic forms under a relative congruence are tested on the transformed vector. -/
theorem sector_gammaFock_congruence_quadratic {n : ℕ} (k : ℕ)
    (S A : Matrix (Fin n) (Fin n) ℂ) (v : Prop5.PhotonSector n k → ℂ) :
    star v ⬝ᵥ (Prop5.sectorBlock k (gammaFock (Sᴴ * A * S)) *ᵥ v) =
      star (Prop5.sectorBlock k (gammaFock S) *ᵥ v) ⬝ᵥ
        (Prop5.sectorBlock k (gammaFock A) *ᵥ (Prop5.sectorBlock k (gammaFock S) *ᵥ v)) := by
  rw [sector_gammaFock_congruence, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

/-- The relative scalar normalization contributes exactly its `k`-th power. -/
theorem sector_gammaFock_relative_quadratic {n : ℕ} (k : ℕ)
    (S A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v : Prop5.PhotonSector n k → ℂ) :
    star v ⬝ᵥ (Prop5.sectorBlock k (gammaFock (c • (Sᴴ * A * S))) *ᵥ v) =
      c ^ k * (star (Prop5.sectorBlock k (gammaFock S) *ᵥ v) ⬝ᵥ
        (Prop5.sectorBlock k (gammaFock A) *ᵥ (Prop5.sectorBlock k (gammaFock S) *ᵥ v))) := by
  rw [sector_gammaFock_smul, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, sector_gammaFock_congruence_quadratic]


theorem finiteQuadraticForm_eq_re_dot {I : Type*} [Fintype I]
    (A : Matrix I I ℂ) (v : I → ℂ) :
    Prop5.finiteQuadraticForm A v = (star v ⬝ᵥ (A *ᵥ v)).re := by
  simp only [Prop5.finiteQuadraticForm, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum, mul_assoc]

theorem finiteQuadraticForm_real_smul {I : Type*} [Fintype I]
    (A : Matrix I I ℂ) (v : I → ℂ) (c : ℝ) :
    Prop5.finiteQuadraticForm ((c : ℂ) • A) v = c * Prop5.finiteQuadraticForm A v := by
  rw [finiteQuadraticForm_eq_re_dot, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, Complex.re_ofReal_mul, finiteQuadraticForm_eq_re_dot]

theorem sector_gammaFock_relative_real_quadratic {n : ℕ} (k : ℕ)
    (S A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (v : Prop5.PhotonSector n k → ℂ) :
    Prop5.finiteQuadraticForm (Prop5.sectorBlock k (gammaFock ((c : ℂ) • (Sᴴ * A * S)))) v =
      c ^ k * Prop5.finiteQuadraticForm (Prop5.sectorBlock k (gammaFock A))
        (Prop5.sectorBlock k (gammaFock S) *ᵥ v) := by
  simp only [finiteQuadraticForm_eq_re_dot]
  rw [sector_gammaFock_relative_quadratic, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem finiteQuadraticForm_one {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℂ) :
    Prop5.finiteQuadraticForm (1 : Matrix I I ℂ) v = ∑ i, ‖v i‖ ^ 2 := by
  rw [finiteQuadraticForm_eq_re_dot, Matrix.one_mulVec]
  simp [dotProduct, Complex.conj_mul', ← Complex.ofReal_pow]

/-- The relative state ratio splits into a scalar normalizer and a normalized
quadratic form of the perturbation alone. -/
theorem sector_gammaFock_relative_ratio {n : ℕ} (k : ℕ)
    (S A : Matrix (Fin n) (Fin n) ℂ) (r d : ℝ) (hr : r ≠ 0) (hd : d ≠ 0)
    (v : Prop5.PhotonSector n k → ℂ)
    (hw : Prop5.sectorBlock k (gammaFock S) *ᵥ v ≠ 0) :
    Prop5.finiteQuadraticForm (Prop5.sectorBlock k (gammaFock (((r / d : ℝ) : ℂ) •
        (Sᴴ * A * S)))) v /
      Prop5.finiteQuadraticForm (Prop5.sectorBlock k (gammaFock ((r : ℂ) • (Sᴴ * S)))) v =
    d⁻¹ ^ k * (Prop5.finiteQuadraticForm (Prop5.sectorBlock k (gammaFock A))
      (Prop5.sectorBlock k (gammaFock S) *ᵥ v) /
      (∑ i, ‖(Prop5.sectorBlock k (gammaFock S) *ᵥ v) i‖ ^ 2)) := by
  classical
  have he : Sᴴ * S = Sᴴ * (1 : Matrix (Fin n) (Fin n) ℂ) * S := by rw [Matrix.mul_one]
  rw [he, sector_gammaFock_relative_real_quadratic,
    sector_gammaFock_relative_real_quadratic, Prop5.sector_gammaFock_one,
    finiteQuadraticForm_one]
  have hwpos : 0 < ∑ i, ‖(Prop5.sectorBlock k (gammaFock S) *ᵥ v) i‖ ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, (Prop5.sectorBlock k (gammaFock S) *ᵥ v) i ≠ 0 := by
      contrapose! hw
      exact funext hw
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_pos (norm_pos_iff.mpr hi)⟩
  field_simp
  simp [div_pow, one_div, div_eq_mul_inv, mul_pow, inv_pow, mul_comm, mul_left_comm, mul_assoc]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop5Geometry -/
section
open scoped ENNReal Matrix ComplexOrder
open BosonicLearn
set_option maxHeartbeats 600000

noncomputable section
namespace Prop5Geometry

/-- The trace norm of a Hermitian matrix is attained on a unitary: `‖H‖₁ = Tr(H W)`. -/
private lemma schatten_one_herm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ, Wᴴ * W = 1 ∧
      WHMultiplicativity.schattenNorm 1 H = (H * W).trace.re := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  set x : Fin n → ℝ := hH.eigenvalues with hx
  have hspec : H = V * Matrix.diagonal (fun i => ((x i : ℝ) : ℂ)) * Vᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  have hcfc : cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) =
      V * Matrix.diagonal (fun i => ((|x i| : ℝ) : ℂ)) * Vᴴ := by
    rw [hH.eq]
    have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
    have h1 : H * H = cfc (fun t : ℝ => t ^ 2) H := by
      rw [cfc_pow_id H 2, pow_two]
    have hc : Continuous (fun t : ℝ => t ^ ((1 : ℝ) / 2)) :=
      Real.continuous_rpow_const (by norm_num)
    rw [h1, ← cfc_comp' (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (fun t : ℝ => t ^ 2) H hc.continuousOn,
      hH.cfc_eq]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, ← hVdef, Matrix.star_eq_conjTranspose]
    have hd : (RCLike.ofReal ∘ (fun t : ℝ => (t ^ 2) ^ ((1 : ℝ) / 2)) ∘ hH.eigenvalues :
        Fin n → ℂ) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      simp only [Function.comp_apply]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rfl
    rw [hd]
  have hnorm : WHMultiplicativity.schattenNorm 1 H =
      (cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H)).trace.re := by
    unfold WHMultiplicativity.schattenNorm
    rw [if_neg ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, div_one]
    rw [Real.rpow_one]
  set s : Fin n → ℝ := fun i => if 0 ≤ x i then 1 else -1 with hs
  have hss : ∀ i, s i * s i = 1 := by
    intro i
    simp only [hs]
    split_ifs <;> norm_num
  have hxs : ∀ i, x i * s i = |x i| := by
    intro i
    simp only [hs]
    split_ifs with h
    · rw [abs_of_nonneg h, mul_one]
    · rw [abs_of_neg (not_le.mp h)]; ring
  set W : Matrix (Fin n) (Fin n) ℂ := V * Matrix.diagonal (fun i => ((s i : ℝ) : ℂ)) * Vᴴ with hW
  have hWh : Wᴴ = W := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    funext i
    simp
  have hmul : ∀ d₁ d₂ : Fin n → ℂ, (V * Matrix.diagonal d₁ * Vᴴ) * (V * Matrix.diagonal d₂ * Vᴴ) =
      V * Matrix.diagonal (fun i => d₁ i * d₂ i) * Vᴴ := by
    intro d₁ d₂
    have h : (V * Matrix.diagonal d₁ * Vᴴ) * (V * Matrix.diagonal d₂ * Vᴴ) =
        V * (Matrix.diagonal d₁ * (Vᴴ * V) * Matrix.diagonal d₂) * Vᴴ := by
      simp only [Matrix.mul_assoc]
    rw [h, hV1, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  refine ⟨W, ?_, ?_⟩
  · rw [hWh, hW, hmul]
    have h1 : (fun i => ((s i : ℝ) : ℂ) * ((s i : ℝ) : ℂ)) = fun _ : Fin n => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, hss i, Complex.ofReal_one]
    rw [h1, Matrix.diagonal_one, Matrix.mul_one, hV2]
  · rw [hnorm, hcfc]
    have h2 : (fun i => ((x i : ℝ) : ℂ) * ((s i : ℝ) : ℂ)) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, hxs i]
    conv_rhs => rw [hspec, hW, hmul, h2]

/-- Hölder-type bound: `|Tr(diag(e) P Q)| ≤ ∑ |eᵢ|` when `P Pᴴ ⪯ 1` and `Qᴴ Q ⪯ 1`. -/
private lemma holder {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ)
    (hP : (1 - P * Pᴴ).PosSemidef) (hQ : (1 - Qᴴ * Q).PosSemidef) :
    |(Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * (P * Q)).trace.re| ≤ ∑ i, |e i| := by
  have hProw : ∀ i, ∑ j, ‖P i j‖ ^ 2 ≤ 1 := by
    intro i
    have h := hP.diag_nonneg (i := i)
    have h2 : (1 - P * Pᴴ) i i = ((1 - ∑ j, ‖P i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']
    rw [h2] at h
    have := Complex.zero_le_real.mp h
    linarith
  have hQcol : ∀ i, ∑ j, ‖Q j i‖ ^ 2 ≤ 1 := by
    intro i
    have h := hQ.diag_nonneg (i := i)
    have h2 : (1 - Qᴴ * Q) i i = ((1 - ∑ j, ‖Q j i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
    rw [h2] at h
    have := Complex.zero_le_real.mp h
    linarith
  have htr : (Matrix.diagonal (fun i => ((e i : ℝ) : ℂ)) * (P * Q)).trace.re =
      ∑ i, e i * ∑ j, (P i j * Q j i).re := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.diagonal_mul]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply, Complex.re_ofReal_mul, Complex.re_sum]
  rw [htr]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hone : |∑ j, (P i j * Q j i).re| ≤ 1 := by
    calc |∑ j, (P i j * Q j i).re| ≤ ∑ j, |(P i j * Q j i).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (‖P i j‖ ^ 2 + ‖Q j i‖ ^ 2) / 2 := Finset.sum_le_sum fun j _ => by
          have h1 : |(P i j * Q j i).re| ≤ ‖P i j‖ * ‖Q j i‖ := by
            rw [← norm_mul]
            exact Complex.abs_re_le_norm _
          nlinarith [sq_nonneg (‖P i j‖ - ‖Q j i‖)]
      _ = (∑ j, ‖P i j‖ ^ 2 + ∑ j, ‖Q j i‖ ^ 2) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ 1 := by linarith [hProw i, hQcol i]
  calc |e i| * |∑ j, (P i j * Q j i).re| ≤ |e i| * 1 :=
        mul_le_mul_of_nonneg_left hone (abs_nonneg _)
    _ = |e i| := mul_one _


theorem schatten_one_herm_eq_sum {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    WHMultiplicativity.schattenNorm 1 H = ∑ i, |hH.eigenvalues i| := by
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ,
      V = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hV1 : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, hVdef]
    exact Unitary.coe_mul_star_self _
  set x : Fin n → ℝ := hH.eigenvalues with hx
  have hspec : H = V * Matrix.diagonal (fun i => ((x i : ℝ) : ℂ)) * Vᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [hVdef, ← Matrix.star_eq_conjTranspose]
    exact h
  have hcfc : cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) =
      V * Matrix.diagonal (fun i => ((|x i| : ℝ) : ℂ)) * Vᴴ := by
    rw [hH.eq]
    have hsa : IsSelfAdjoint H := hH.isSelfAdjoint
    have h1 : H * H = cfc (fun t : ℝ => t ^ 2) H := by
      rw [cfc_pow_id H 2, pow_two]
    have hc : Continuous (fun t : ℝ => t ^ ((1 : ℝ) / 2)) :=
      Real.continuous_rpow_const (by norm_num)
    rw [h1, ← cfc_comp' (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (fun t : ℝ => t ^ 2) H hc.continuousOn,
      hH.cfc_eq]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, ← hVdef, Matrix.star_eq_conjTranspose]
    have hd : (RCLike.ofReal ∘ (fun t : ℝ => (t ^ 2) ^ ((1 : ℝ) / 2)) ∘ hH.eigenvalues :
        Fin n → ℂ) = fun i => ((|x i| : ℝ) : ℂ) := by
      funext i
      simp only [Function.comp_apply]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rfl
    rw [hd]
  have hnorm : WHMultiplicativity.schattenNorm 1 H =
      (cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H)).trace.re := by
    unfold WHMultiplicativity.schattenNorm
    rw [if_neg ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, div_one]
    rw [Real.rpow_one]
  rw [hnorm, hcfc, Matrix.trace_mul_cycle, hV1, Matrix.one_mul,
    Matrix.trace_diagonal, Complex.re_sum]
  simp [hx]

private lemma trace_mul_unitary_le {n : ℕ}
    (H W : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hW : Wᴴ * W = 1) :
    (H * W).trace.re ≤ WHMultiplicativity.schattenNorm 1 H := by
  let V : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  have hV1 : Vᴴ * V = 1 := by
    exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hV2 : V * Vᴴ = 1 := by
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hW2 : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hspec : H = V * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
    simpa [V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using hH.spectral_theorem
  have hp : (1 - (Vᴴ * W) * (Vᴴ * W)ᴴ).PosSemidef := by
    have heq : (Vᴴ * W) * (Vᴴ * W)ᴴ = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc (Vᴴ * W) * (Wᴴ * V) = Vᴴ * (W * Wᴴ) * V := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hW2, Matrix.mul_one, hV1]
    rw [heq, sub_self]; exact Matrix.PosSemidef.zero
  have hq : (1 - Vᴴ * V).PosSemidef := by
    rw [hV1, sub_self]; exact Matrix.PosSemidef.zero
  have hb := holder (Vᴴ * W) V hH.eigenvalues hp hq
  rw [schatten_one_herm_eq_sum H hH]
  calc (H * W).trace.re =
      (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * ((Vᴴ * W) * V)).trace.re := by
        conv_lhs => rw [hspec]
        congr 1
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm V]
        simp only [Matrix.mul_assoc]
    _ ≤ |(Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * ((Vᴴ * W) * V)).trace.re| := le_abs_self _
    _ ≤ ∑ i, |hH.eigenvalues i| := hb

/-- Triangle inequality for the trace norm of Hermitian matrices. -/
theorem schatten_one_add_le {n : ℕ}
    (H K : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    WHMultiplicativity.schattenNorm 1 (H + K) ≤
      WHMultiplicativity.schattenNorm 1 H + WHMultiplicativity.schattenNorm 1 K := by
  obtain ⟨W, hW, hnorm⟩ := schatten_one_herm (H + K) (hH.add hK)
  rw [hnorm, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  exact add_le_add (trace_mul_unitary_le H W hH hW) (trace_mul_unitary_le K W hK hW)

/-- The trace norm is unchanged by negating a matrix. -/
theorem schatten_one_neg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 1 (-H) = WHMultiplicativity.schattenNorm 1 H := by
  simp [WHMultiplicativity.schattenNorm]

open scoped Matrix.Norms.L2Operator in
/-- The finite-dimensional trace norm is continuous. -/
theorem continuous_schatten_one (n : ℕ) :
    Continuous fun H : Matrix (Fin n) (Fin n) ℂ => WHMultiplicativity.schattenNorm 1 H := by
  have hmul : Continuous fun H : Matrix (Fin n) (Fin n) ℂ => Hᴴ * H :=
    continuous_id.matrix_conjTranspose.mul continuous_id
  have hcfc : Continuous fun H : Matrix (Fin n) (Fin n) ℂ =>
      cfc (fun t : ℝ => t ^ ((1 : ℝ) / 2)) (Hᴴ * H) := by
    exact hmul.cfc_of_mem_nhdsSet (s := Set.univ) (fun t : ℝ => t ^ ((1 : ℝ) / 2))
      (by simp)
      (ha' := fun H => (Matrix.posSemidef_conjTranspose_mul_self H).isHermitian.isSelfAdjoint)
      (hf := (Real.continuous_rpow_const (by norm_num)).continuousOn)
  convert Complex.continuous_re.comp hcfc.matrix_trace using 1
  ext H
  simp [WHMultiplicativity.schattenNorm]

/-- Symmetry of the trace-norm distance on traceless Hermitian matrices. -/
theorem trace_distance_symm {n : ℕ} (X Y : Herm0 n) :
    WHMultiplicativity.schattenNorm 1 ((X - Y : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) =
      WHMultiplicativity.schattenNorm 1 ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
  change WHMultiplicativity.schattenNorm 1 ((X : Matrix (Fin n) (Fin n) ℂ) -
    (Y : Matrix (Fin n) (Fin n) ℂ)) =
      WHMultiplicativity.schattenNorm 1 ((Y : Matrix (Fin n) (Fin n) ℂ) -
        (X : Matrix (Fin n) (Fin n) ℂ))
  rw [← neg_sub (Y : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
    schatten_one_neg]

/-- Triangle inequality in exactly the parameter space used by Proposition 5. -/
theorem trace_distance_triangle {n : ℕ} (X Y Z : Herm0 n) :
    WHMultiplicativity.schattenNorm 1 ((X - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤
      WHMultiplicativity.schattenNorm 1 ((X - Y : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) +
      WHMultiplicativity.schattenNorm 1 ((Y - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
  have h := schatten_one_add_le
    ((X - Y : Herm0 n) : Matrix (Fin n) (Fin n) ℂ)
    ((Y - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ)
    (X - Y).property.1 (Y - Z).property.1
  simpa only [Submodule.coe_sub, sub_add_sub_cancel] using h

/-- Two points in a trace ball of radius `r` have mutual distance at most `2r`. -/
theorem trace_ball_pair {n : ℕ} (X Y Z : Herm0 n) (r : ℝ)
    (hX : WHMultiplicativity.schattenNorm 1
      ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r)
    (hZ : WHMultiplicativity.schattenNorm 1
      ((Y - Z : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r) :
    WHMultiplicativity.schattenNorm 1
      ((Z - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ 2 * r := by
  have ht := trace_distance_triangle Z Y X
  rw [trace_distance_symm Z Y] at ht
  linarith

/-- Joint measurability of trace-norm distance. -/
theorem measurable_trace_distance (n : ℕ) :
    Measurable fun XY : Herm0 n × Herm0 n => WHMultiplicativity.schattenNorm 1
      ((XY.1 - XY.2 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
  have : SecondCountableTopology (Herm0 n) :=
    @TopologicalSpace.Subtype.secondCountableTopology (Fin n → Fin n → ℂ) _
      (fun X => X ∈ Herm0 n) inferInstance
  apply Continuous.measurable
  exact (continuous_schatten_one n).comp
    ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd))

/-- The trace-distance relation at a fixed radius is a Borel set. -/
theorem measurableSet_trace_relation (n : ℕ) (r : ℝ) :
    MeasurableSet {XY : Herm0 n × Herm0 n | WHMultiplicativity.schattenNorm 1
      ((XY.1 - XY.2 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r} :=
  measurableSet_le (measurable_trace_distance n) measurable_const

/-- Trace balls are measurable, including for an arbitrary real radius. -/
theorem measurableSet_trace_ball {n : ℕ} (X : Herm0 n) (r : ℝ) :
    MeasurableSet {Y : Herm0 n | WHMultiplicativity.schattenNorm 1
      ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ r} := by
  have hc : Continuous fun Y : Herm0 n => WHMultiplicativity.schattenNorm 1
      ((Y - X : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) :=
    (continuous_schatten_one n).comp (continuous_subtype_val.sub continuous_const)
  exact (isClosed_le hc continuous_const).measurableSet

end Prop5Geometry

end
end

/- Local helper source: Definitions.Def_BosonicLearn_tracelessGUE -/
section
open MeasureTheory

namespace BosonicLearn

/-- Unnormalized traceless-GUE density in the convention of Definition 6 and
Equation (32) of Chen--Mele--Mele--Preskill, arXiv:2609.26705. Its covariance
on the real Hilbert space of traceless Hermitian matrices is `2/n` times the
identity. The arbitrary normalization of additive Haar measure cancels below. -/
noncomputable def tracelessGUEWeight (n : ℕ) : Measure (Herm0 n) :=
  (Measure.addHaar : Measure (Herm0 n)).withDensity
    (fun X => ENNReal.ofReal (Real.exp (-(n / 4 : ℝ) *
      WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)))

/-- The normalized, unconditioned traceless Gaussian unitary ensemble.
This is the law of `G - (Tr G/n) I` when `G` has diagonal variance `2/n`
and independent real/imaginary off-diagonal variances `1/n`.
The equivalence with independent coordinates is mathematical background;
this definition fixes the density directly. -/
noncomputable def tracelessGUE (n : ℕ) : Measure (Herm0 n) :=
  ProbabilityTheory.cond (tracelessGUEWeight n) Set.univ

end BosonicLearn

end

/- Local helper source: Solutions.Prop5Prior -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BosonicLearn.Prop5

/-- Conditioning on a superset of a good event cannot increase its failure probability. -/
theorem cond_superset_compl_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G S : Set Ω) (hG : MeasurableSet G) (hS : MeasurableSet S) (hGS : G ⊆ S) :
    ProbabilityTheory.cond μ S Gᶜ ≤ μ Gᶜ := by
  by_cases hzero : μ S = 0
  · rw [cond_eq_zero_of_meas_eq_zero hzero]
    simp
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ S) := cond_isProbabilityMeasure hzero
  rw [prob_compl_eq_one_sub hG, prob_compl_eq_one_sub hG]
  apply tsub_le_tsub_left
  rw [cond_apply hS, Set.inter_eq_right.mpr hGS]
  calc
    μ G = 1 * μ G := (one_mul _).symm
    _ ≤ (μ S)⁻¹ * μ G := mul_le_mul' (ENNReal.one_le_inv.mpr prob_le_one) le_rfl

/-- The same conditioning comparison for an arbitrary finite unnormalized law. -/
theorem cond_superset_compl_le_normalized {Ω : Type*} [MeasurableSpace Ω]
    (m : Measure Ω) (hfin : m Set.univ ≠ ⊤)
    (G S : Set Ω) (hG : MeasurableSet G) (hS : MeasurableSet S) (hGS : G ⊆ S) :
    ProbabilityTheory.cond m S Gᶜ ≤ ProbabilityTheory.cond m Set.univ Gᶜ := by
  by_cases hzero : m Set.univ = 0
  · have hm : m = 0 := Measure.measure_univ_eq_zero.mp hzero
    simp [hm, ProbabilityTheory.cond]
  have : IsProbabilityMeasure (ProbabilityTheory.cond m Set.univ) :=
    cond_isProbabilityMeasure_of_finite hzero hfin
  have h := cond_superset_compl_le (ProbabilityTheory.cond m Set.univ) G S hG hS hGS
  have heq : ProbabilityTheory.cond (ProbabilityTheory.cond m Set.univ) S = ProbabilityTheory.cond m S := by
    simpa using cond_cond_eq_cond_inter' MeasurableSet.univ hS hfin
  simpa only [heq] using h

/-- Local abbreviation for the reusable unconditioned Gaussian density. -/
noncomputable abbrev gueWeight (n : ℕ) : Measure (Herm0 n) := tracelessGUEWeight n

/-- The prior is exactly the traceless Gaussian density conditioned on `Gsupp`. -/
theorem priorMu_eq_cond_gueWeight (n : ℕ) :
    priorMu n = ProbabilityTheory.cond (gueWeight n) (Gsupp n) := by
  have hs : MeasurableSet (Gsupp n) := by
    have hc : Continuous fun X : Herm0 n =>
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
      apply Continuous.norm
      exact (LinearMap.continuous_of_finiteDimensional
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
          continuous_subtype_val
    simpa [Gsupp, WHMultiplicativity.schattenNorm] using
      measurableSet_le hc.measurable measurable_const
  unfold priorMu ProbabilityTheory.cond gueWeight tracelessGUEWeight
  dsimp only
  rw [← restrict_withDensity hs, Measure.restrict_apply_univ]

/-- The prior's bad-set mass is no larger than the unconditioned traceless-GUE
bad-set mass. No loss in the exponential rate is needed. -/
theorem prior_bad_le_gue_bad (n : ℕ) (hfin : gueWeight n Set.univ ≠ ⊤) :
    priorMu n (Ggood n)ᶜ ≤ ProbabilityTheory.cond (gueWeight n) Set.univ (Ggood n)ᶜ := by
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  have hG : MeasurableSet (Ggood n) := by
    simpa [Ggood, WHMultiplicativity.schattenNorm] using
      measurableSet_le hc.measurable measurable_const
  have hS : MeasurableSet (Gsupp n) := by
    simpa [Gsupp, WHMultiplicativity.schattenNorm] using
      measurableSet_le hc.measurable measurable_const
  rw [priorMu_eq_cond_gueWeight]
  apply cond_superset_compl_le_normalized (gueWeight n) hfin (Ggood n) (Gsupp n) hG hS
  intro X hX
  exact le_trans hX (by norm_num : (3 : ℝ) ≤ 4)


/-- A radial Gaussian is integrable for any finite-dimensional real norm. -/
theorem integrable_exp_neg_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : Measure E) [m.IsAddHaarMeasure] (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : E => Real.exp (-b * ‖x‖ ^ 2)) m := by
  rcases subsingleton_or_nontrivial E with hsub | hnon
  · have : CompactSpace E := ⟨Set.finite_univ.isCompact⟩
    have : IsFiniteMeasure m := ⟨isCompact_univ.measure_lt_top⟩
    have hconst : (fun x : E => Real.exp (-b * ‖x‖ ^ 2)) = fun _ => (1 : ℝ) := by
      funext x
      rw [Subsingleton.elim x 0]
      simp
    rw [hconst]
    exact integrable_const 1
  · apply (integrable_fun_norm_addHaar m (f := fun r : ℝ => Real.exp (-b * r ^ 2))).mpr
    simpa only [smul_eq_mul, Real.rpow_natCast] using
      integrableOn_rpow_mul_exp_neg_mul_sq hb
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))


/-- Frobenius norm in the published Schatten convention. -/
theorem schatten_two_eq_sqrt (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 X = Real.sqrt (∑ i, ∑ j, ‖X j i‖ ^ 2) := by
  unfold WHMultiplicativity.schattenNorm
  rw [if_neg (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2]
  have hfun : (fun x : ℝ => x ^ ((2 : ℝ) / 2)) = fun x => x := by
    funext x
    rw [div_self (by norm_num), Real.rpow_one]
  rw [hfun, cfc_id' ℝ (X.conjTranspose * X)
    (by rw [← Matrix.star_eq_conjTranspose]; exact IsSelfAdjoint.star_mul_self X)]
  rw [Real.sqrt_eq_rpow]
  congr 1
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.conj_mul', ← Complex.ofReal_pow]


/-- The entrywise supremum norm is bounded by the Frobenius norm. -/
theorem norm_le_schatten_two (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖fun i j => X i j‖ ≤ WHMultiplicativity.schattenNorm 2 X := by
  rw [schatten_two_eq_sqrt]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  have hs : (0 : ℝ) ≤ ∑ a, ∑ b, ‖X b a‖ ^ 2 := by positivity
  have h1 : ‖X i j‖ ^ 2 ≤ ∑ b, ‖X b j‖ ^ 2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg (‖X b j‖)) (Finset.mem_univ i)
  have h2 : (∑ b, ‖X b j‖ ^ 2) ≤ ∑ a, ∑ b, ‖X b a‖ ^ 2 :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (‖X b a‖))) (Finset.mem_univ j)
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ a, ∑ b, ‖X b a‖ ^ 2), norm_nonneg (X i j)]

/-- The unconditioned traceless-GUE density has finite mass. -/
theorem gueWeight_finite (n : ℕ) (hn : 0 < n) : gueWeight n Set.univ ≠ ⊤ := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  have hi := integrable_exp_neg_norm_sq (Measure.addHaar : Measure (Herm0 n))
    (n / 4 : ℝ) (by positivity)
  let f : Herm0 n → ℝ := fun X => Real.exp (-(n / 4 : ℝ) *
    WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)
  have hcont : Continuous f := by
    dsimp only [f]
    simp_rw [schatten_two_eq_sqrt]
    have he : ∀ i j : Fin n, Continuous (fun X : Herm0 n => (X : Matrix (Fin n) (Fin n) ℂ) i j) :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    apply Real.continuous_exp.comp
    apply Continuous.mul continuous_const
    apply Continuous.pow
    apply Real.continuous_sqrt.comp
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    exact (he j i).norm.pow 2
  have hint : Integrable f (Measure.addHaar : Measure (Herm0 n)) := by
    apply hi.mono' hcont.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro X
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hX := norm_le_schatten_two n (X : Matrix (Fin n) (Fin n) ℂ)
    have hF : 0 ≤ WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) := by
      rw [schatten_two_eq_sqrt]
      positivity
    have hb : (0 : ℝ) ≤ n / 4 := by positivity
    change ‖X‖ ≤ WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) at hX
    have hsq : ‖X‖ ^ 2 ≤ WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2 := by
      nlinarith [norm_nonneg X]
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hsq hb)
  have hf : ∀ᵐ X ∂(Measure.addHaar : Measure (Herm0 n)), 0 ≤ f X :=
    Filter.Eventually.of_forall (fun X => (Real.exp_pos _).le)
  have hfin := (hasFiniteIntegral_iff_ofReal hf).mp hint.hasFiniteIntegral
  unfold gueWeight tracelessGUEWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hfin.ne


/-- The Gaussian weight has positive mass in every dimension. -/
theorem gueWeight_pos (n : ℕ) : 0 < gueWeight n Set.univ := by
  let f : Herm0 n → ℝ≥0∞ := fun X => ENNReal.ofReal (Real.exp (-(n / 4 : ℝ) *
    WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2))
  have hf : Measurable f := by
    dsimp only [f]
    simp_rw [schatten_two_eq_sqrt]
    apply Continuous.measurable
    apply ENNReal.continuous_ofReal.comp
    apply Real.continuous_exp.comp
    apply Continuous.mul continuous_const
    apply Continuous.pow
    apply Real.continuous_sqrt.comp
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    have he : Continuous (fun X : Herm0 n => (X : Matrix (Fin n) (Fin n) ℂ) j i) :=
      (continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val)
    exact he.norm.pow 2
  have hpos : ∀ X, 0 < f X := fun X => ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hsupp : Function.support f = Set.univ := by
    ext X
    simp [Function.mem_support, (hpos X).ne']
  unfold gueWeight tracelessGUEWeight
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change 0 < ∫⁻ X, f X ∂(Measure.addHaar : Measure (Herm0 n))
  rw [lintegral_pos_iff_support hf, hsupp]
  exact isOpen_univ.measure_pos _ ⟨0, Set.mem_univ _⟩

/-- The normalized unconditioned density is a genuine probability law. -/
theorem gue_probability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (ProbabilityTheory.cond (gueWeight n) Set.univ) :=
  cond_isProbabilityMeasure_of_finite (gueWeight_pos n).ne' (gueWeight_finite n hn)

/-- The conditioning bridge with normalization discharged. -/
theorem prior_bad_le_gue_bad_of_pos (n : ℕ) (hn : 0 < n) :
    priorMu n (Ggood n)ᶜ ≤ ProbabilityTheory.cond (gueWeight n) Set.univ (Ggood n)ᶜ :=
  prior_bad_le_gue_bad n (gueWeight_finite n hn)

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop5GUEGeometry -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Prop5

section Rayleigh
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The supremum of Rayleigh quotients, including zero. On a nonzero traceless
Hermitian operator this is its largest eigenvalue. -/
noncomputable def upperRayleigh (T : E →L[ℂ] E) : ℝ := ⨆ v, T.rayleighQuotient v

lemma bddAbove_rayleigh (T : E →L[ℂ] E) : BddAbove (Set.range T.rayleighQuotient) :=
  ⟨‖T‖, fun _ ⟨v, hv⟩ => hv ▸ (le_abs_self _).trans (T.rayleighQuotient_le_norm v)⟩

lemma rayleigh_le_upperRayleigh (T : E →L[ℂ] E) (v : E) :
    T.rayleighQuotient v ≤ upperRayleigh T := le_ciSup (bddAbove_rayleigh T) v

lemma upperRayleigh_nonneg (T : E →L[ℂ] E) : 0 ≤ upperRayleigh T := by
  simpa using rayleigh_le_upperRayleigh T 0

lemma upperRayleigh_le_norm (T : E →L[ℂ] E) : upperRayleigh T ≤ ‖T‖ := by
  apply ciSup_le
  intro v
  exact (le_abs_self _).trans (T.rayleighQuotient_le_norm v)

lemma upperRayleigh_le_add_norm_sub (T S : E →L[ℂ] E) :
    upperRayleigh T ≤ upperRayleigh S + ‖T - S‖ := by
  apply ciSup_le
  intro v
  have heq : T.rayleighQuotient v = S.rayleighQuotient v + (T - S).rayleighQuotient v := by
    rw [← ContinuousLinearMap.rayleighQuotient_add]
    congr 1
    abel
  rw [heq]
  exact add_le_add (rayleigh_le_upperRayleigh S v)
    ((le_abs_self _).trans ((T - S).rayleighQuotient_le_norm v))

/-- Rayleigh maxima are 1-Lipschitz for operator norm. -/
theorem upperRayleigh_lipschitz (T S : E →L[ℂ] E) :
    |upperRayleigh T - upperRayleigh S| ≤ ‖T - S‖ := by
  have h1 := upperRayleigh_le_add_norm_sub T S
  have h2 := upperRayleigh_le_add_norm_sub S T
  rw [norm_sub_rev S T] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Both signs of the Rayleigh maximum control a self-adjoint operator norm. -/
theorem norm_le_max_upperRayleigh (T : E →L[ℂ] E) (hT : T.IsSymmetric) :
    ‖T‖ ≤ max (upperRayleigh T) (upperRayleigh (-T)) := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro v
  have h1 := rayleigh_le_upperRayleigh T v
  have h2 := rayleigh_le_upperRayleigh (-T) v
  rw [ContinuousLinearMap.rayleighQuotient_neg_apply] at h2
  exact abs_le.mpr ⟨by linarith [le_max_right (upperRayleigh T) (upperRayleigh (-T))],
    h1.trans (le_max_left _ _)⟩

end Rayleigh


open scoped Matrix.Norms.Frobenius in
/-- The published Schatten 2-norm agrees with the matrix Frobenius norm. -/
theorem schatten_two_eq_frobenius (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 X = ‖X‖ := by
  rw [schatten_two_eq_sqrt, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  rw [Finset.sum_comm]
  simp only [Real.rpow_two]

open scoped Matrix.Norms.Frobenius in
/-- Euclidean operator norm is bounded by the Frobenius norm. -/
theorem operator_norm_le_schatten_two (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ ≤ WHMultiplicativity.schattenNorm 2 X := by
  rw [schatten_two_eq_frobenius]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
  intro v
  have h := Matrix.frobenius_norm_mul X (Matrix.replicateCol Unit (WithLp.ofLp v))
  rw [← Matrix.replicateCol_mulVec, Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at h
  exact h

/-- The largest Rayleigh quotient is 1-Lipschitz in the Frobenius metric. -/
theorem matrix_upperRayleigh_lipschitz (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    |upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ) X) -
      upperRayleigh (Matrix.toEuclideanCLM (𝕜 := ℂ) Y)| ≤
      WHMultiplicativity.schattenNorm 2 (X - Y) := by
  refine (upperRayleigh_lipschitz _ _).trans ?_
  rw [← map_sub]
  exact operator_norm_le_schatten_two n (X - Y)

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5TraceFrobenius -/
section
open scoped Matrix ComplexOrder ENNReal
open BosonicLearn

noncomputable section
namespace BosonicLearn.Prop5

/-- Each Hermitian eigenvalue is bounded by the Euclidean operator norm. -/
theorem abs_eigenvalue_le_operator_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (i : Fin n) :
    |hA.eigenvalues i| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ := by
  let v := hA.eigenvectorBasis i
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) A
  have hv : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hd : star v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) = inner ℂ v (T v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM,
      dotProduct_comm]
  rw [hA.eigenvalues_eq]
  change |(star v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)).re| ≤ _
  rw [hd]
  calc
    |(inner ℂ v (T v)).re| ≤ ‖inner ℂ v (T v)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖T‖ * ‖v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg v)
    _ = ‖T‖ := by rw [hv]; ring

/-- Squared Schatten 2-norm is the trace of the Gram matrix. -/
theorem schatten_two_sq_eq_trace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 A ^ 2 = (Aᴴ * A).trace.re := by
  rw [schatten_two_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg ‖A j i‖)]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.conj_mul', ← Complex.ofReal_pow]

/-- Squared Frobenius norm is the sum of squared Hermitian eigenvalues. -/
theorem schatten_two_sq_eq_eigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    WHMultiplicativity.schattenNorm 2 A ^ 2 = ∑ i, (hA.eigenvalues i) ^ 2 := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have hsq : A * A = cfc (fun t : ℝ => t ^ 2) A := by
    rw [cfc_pow_id A 2, pow_two]
  rw [schatten_two_sq_eq_trace, hA.eq, hsq, hA.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp [← Complex.ofReal_pow]

/-- The Schatten interpolation bound needed to turn trace balls into Frobenius balls. -/
theorem schatten_two_sq_le_top_mul_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    WHMultiplicativity.schattenNorm 2 A ^ 2 ≤
      WHMultiplicativity.schattenNorm ⊤ A * WHMultiplicativity.schattenNorm 1 A := by
  rw [schatten_two_sq_eq_eigenvalues A hA, Prop5Geometry.schatten_one_herm_eq_sum A hA,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have he := abs_eigenvalue_le_operator_norm A hA i
  have hm := mul_le_mul_of_nonneg_right he (abs_nonneg (hA.eigenvalues i))
  change hA.eigenvalues i ^ 2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ * |hA.eigenvalues i|
  nlinarith [sq_abs (hA.eigenvalues i)]

/-- Near a good center, trace radius `n*a` implies squared Frobenius radius `7*n*a`. -/
theorem trace_ball_frobenius_sq_bound {n : ℕ} (X X₀ : Herm0 n)
    (hX : X ∈ Gsupp n) (hX₀ : X₀ ∈ Ggood n) (a : ℝ)
    (ha : WHMultiplicativity.schattenNorm 1
      ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a) :
    WHMultiplicativity.schattenNorm 2
      ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ^ 2 ≤ 7 * n * a := by
  have hop : WHMultiplicativity.schattenNorm ⊤
      ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ 7 := by
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((X : Matrix (Fin n) (Fin n) ℂ) - (X₀ : Matrix (Fin n) (Fin n) ℂ))‖ ≤ _
    rw [map_sub]
    have h := norm_sub_le (Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (X₀ : Matrix (Fin n) (Fin n) ℂ))
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 4 at hX
    change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X₀ : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 at hX₀
    linarith
  have hn1 : 0 ≤ WHMultiplicativity.schattenNorm 1
      ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Prop5Geometry.schatten_one_herm_eq_sum _ (X - X₀).property.1]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc
    _ ≤ WHMultiplicativity.schattenNorm ⊤
        ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) *
      WHMultiplicativity.schattenNorm 1
        ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) :=
      schatten_two_sq_le_top_mul_one _ (X - X₀).property.1
    _ ≤ 7 * WHMultiplicativity.schattenNorm 1
        ((X - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) :=
      mul_le_mul_of_nonneg_right hop hn1
    _ ≤ 7 * (n * a) := mul_le_mul_of_nonneg_left ha (by norm_num)
    _ = _ := by ring

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop2Determinant -/
section
open scoped Matrix ComplexOrder ENNReal

namespace BosonicLearn.Prop2
noncomputable section

/-- A quadratic remainder estimate requiring only the elementary logarithm bound. -/
theorem log_one_sub_bounds (x : ℝ) (hx : |x| ≤ 1 / 2) :
    -x - 2 * x ^ 2 ≤ Real.log (1 - x) ∧ Real.log (1 - x) ≤ -x := by
  have hxle := (abs_le.mp hx).2
  have hpos : 0 < 1 - x := by linarith
  have hlow := Real.one_sub_inv_le_log_of_pos hpos
  have hupp := Real.log_le_sub_one_of_pos hpos
  refine ⟨?_, by linarith⟩
  apply le_trans _ hlow
  have hid : 1 - (1 - x)⁻¹ = -x - x ^ 2 / (1 - x) := by
    field_simp <;> ring
  rw [hid]
  have hd : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]
  linarith

/-- Traceless first-order perturbations have a nonpositive log determinant,
whose loss is quadratic. -/
theorem log_product_one_sub_bounds {I : Type*} [Fintype I]
    (x : I → ℝ) (hsum : ∑ i, x i = 0) (hx : ∀ i, |x i| ≤ 1 / 2) :
    -(2 * ∑ i, x i ^ 2) ≤ Real.log (∏ i : I, (1 - x i)) ∧
      Real.log (∏ i : I, (1 - x i)) ≤ 0 := by
  classical
  have hpos : ∀ i, 0 < 1 - x i := fun i => by
    have := (abs_le.mp (hx i)).2
    linarith
  rw [Real.log_prod (fun i _ => (hpos i).ne')]
  have hl := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (log_one_sub_bounds (x i) (hx i)).1)
  have hu := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (log_one_sub_bounds (x i) (hx i)).2)
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hsum,
    neg_zero, zero_sub] at hl hu
  exact ⟨hl, hu⟩

/-- The determinant of a real function of a Hermitian matrix is the product
of that function evaluated at the eigenvalues. -/
theorem det_cfc_eq_prod {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).det = ((∏ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  have hu := congrArg Matrix.det (Unitary.coe_mul_star_self hA.eigenvectorUnitary)
  rw [Matrix.det_mul, Matrix.det_one] at hu
  change (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).det *
    (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)).det = 1 at hu
  rw [mul_assoc, mul_comm (Matrix.det (Matrix.diagonal _)), ← mul_assoc, hu, one_mul,
    Matrix.det_diagonal]
  simp [Function.comp_def, Complex.ofReal_prod]

theorem det_one_sub_smul_eq_prod {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (q : ℝ) :
    (1 - (q : ℂ) • A).det = ((∏ i : Fin n, (1 - q * hA.eigenvalues i) : ℝ) : ℂ) := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have he : cfc (fun x : ℝ => 1 - q * x) A = 1 - (q : ℂ) • A := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x => q * x) A
      continuous_const.continuousOn (continuous_const.mul continuous_id).continuousOn,
      cfc_const (1 : ℝ) A, cfc_const_mul_id q A, map_one]
    rfl
  rw [← he]
  exact det_cfc_eq_prod A hA _

/-- The uniform log-determinant bound for a traceless Hermitian matrix. -/
theorem log_det_one_sub_smul_bounds {n : ℕ} (X : Herm0 n) (R q : ℝ)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (hqR : q * R ≤ 1 / 2)
    (hX : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ R) :
    -(2 * (n : ℝ) * q ^ 2 * R ^ 2) ≤
        Real.log ((1 - (q : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)).det.re) ∧
      Real.log ((1 - (q : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)).det.re) ≤ 0 := by
  let eig := X.property.1.eigenvalues
  have heig : ∀ i, |eig i| ≤ R := fun i =>
    (Prop5.abs_eigenvalue_le_operator_norm _ X.property.1 i).trans hX
  have hsum : ∑ i, eig i = 0 := by
    have h := congrArg Complex.re X.property.1.trace_eq_sum_eigenvalues
    simpa [eig, X.property.2] using h.symm
  have hsumq : ∑ i, q * eig i = 0 := by rw [← Finset.mul_sum, hsum, mul_zero]
  have hqx : ∀ i, |q * eig i| ≤ 1 / 2 := by
    intro i
    rw [abs_mul, abs_of_nonneg hq]
    exact (mul_le_mul_of_nonneg_left (heig i) hq).trans hqR
  have hb := log_product_one_sub_bounds (fun i => q * eig i) hsumq hqx
  rw [det_one_sub_smul_eq_prod _ X.property.1, Complex.ofReal_re]
  refine ⟨?_, hb.2⟩
  apply le_trans _ hb.1
  have hsq : ∑ i, (q * eig i) ^ 2 ≤ (n : ℝ) * q ^ 2 * R ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, q ^ 2 * R ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (abs_nonneg _) hR |>.mpr (heig i) |>
          (by simpa only [sq_abs] using ·)) (sq_nonneg q)
      _ = _ := by simp; ring
  linarith


/-- Positivity of the determinant throughout the small spectral perturbation domain. -/
theorem det_one_sub_smul_re_pos {n : ℕ} (X : Herm0 n) (R q : ℝ)
    (hq : 0 ≤ q) (hqR : q * R ≤ 1 / 2)
    (hX : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ R) :
    0 < ((1 - (q : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)).det.re) := by
  rw [det_one_sub_smul_eq_prod _ X.property.1, Complex.ofReal_re]
  apply Finset.prod_pos
  intro i hi
  have he := (Prop5.abs_eigenvalue_le_operator_norm _ X.property.1 i).trans hX
  have hqe := mul_le_mul_of_nonneg_left ((le_abs_self _).trans he) hq
  linarith

/-- Extract the state-independent scalar from a fugacity determinant. -/
theorem log_det_scalar_family {n : ℕ} (X : Herm0 n) (r ξ R : ℝ)
    (hr : r < 1) (hq : 0 ≤ r * ξ / (1 - r))
    (hqR : (r * ξ / (1 - r)) * R ≤ 1 / 2)
    (hX : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ R) :
    Real.log ((1 - (r : ℂ) • (1 + (ξ : ℂ) •
        (X : Matrix (Fin n) (Fin n) ℂ))).det.re) =
      (n : ℝ) * Real.log (1 - r) +
        Real.log ((1 - ((r * ξ / (1 - r) : ℝ) : ℂ) •
          (X : Matrix (Fin n) (Fin n) ℂ)).det.re) := by
  let q := r * ξ / (1 - r)
  have hc : 0 < 1 - r := sub_pos.mpr hr
  have hqdef : (1 - r) * q = r * ξ := by
    dsimp [q]
    field_simp
  have he : (1 : Matrix (Fin n) (Fin n) ℂ) - (r : ℂ) • (1 + (ξ : ℂ) •
        (X : Matrix (Fin n) (Fin n) ℂ)) =
      ((1 - r : ℝ) : ℂ) • (1 - (q : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    push_cast
    have hqc : (1 - (r : ℂ)) * (q : ℂ) = (r : ℂ) * (ξ : ℂ) := by exact_mod_cast hqdef
    linear_combination (X : Matrix (Fin n) (Fin n) ℂ) i j * hqc
  rw [he, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Real.log_mul (pow_ne_zero _ hc.ne') (det_one_sub_smul_re_pos X R q hq hqR hX).ne',
    Real.log_pow]

/-- Uniform comparison of determinant normalizers, retaining the relative scalar parameter. -/
theorem log_det_scalar_family_sub_lower {n : ℕ} (X Y : Herm0 n)
    (hX : X ∈ Gsupp n) (hY : Y ∈ Gsupp n) (r ξ : ℝ)
    (hr : r < 1) (hq : 0 ≤ r * ξ / (1 - r)) (hqle : r * ξ / (1 - r) ≤ 1 / 8) :
    -(32 * (n : ℝ) * (r * ξ / (1 - r)) ^ 2) ≤
      Real.log ((1 - (r : ℂ) • (1 + (ξ : ℂ) •
        (X : Matrix (Fin n) (Fin n) ℂ))).det.re) -
      Real.log ((1 - (r : ℂ) • (1 + (ξ : ℂ) •
        (Y : Matrix (Fin n) (Fin n) ℂ))).det.re) := by
  have hq4 : (r * ξ / (1 - r)) * 4 ≤ 1 / 2 := by linarith
  rw [log_det_scalar_family X r ξ 4 hr hq hq4 hX,
    log_det_scalar_family Y r ξ 4 hr hq hq4 hY]
  have hl := (log_det_one_sub_smul_bounds X 4 _ (by norm_num) hq hq4 hX).1
  have hu := (log_det_one_sub_smul_bounds Y 4 _ (by norm_num) hq hq4 hY).2
  nlinarith


/-- The relative fugacity parameter is at most `2 ν ξ` in the hard-family regime. -/
theorem family_relative_parameter_bounds (ν ξ : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32) :
    let r := ν / ((1 - 4 * ξ) * (1 + ν))
    r < 1 ∧ 0 ≤ r * ξ / (1 - r) ∧ r * ξ / (1 - r) ≤ 2 * ν * ξ ∧
      r * ξ / (1 - r) ≤ 1 / 8 := by
  let d := (1 - 4 * ξ) * (1 + ν)
  have hd : 0 < d := mul_pos (by linarith) (by linarith)
  have hξν : ξ * ν ≤ ξ := by simpa using mul_le_mul_of_nonneg_left hν1 hξ.le
  have hdν : 1 / 2 ≤ d - ν := by dsimp [d]; nlinarith
  have hdνpos : 0 < d - ν := by linarith
  let r := ν / d
  have hr : r < 1 := (div_lt_one hd).mpr (by linarith)
  have hrpos : 0 < r := div_pos hν hd
  have hc : 0 < 1 - r := sub_pos.mpr hr
  have he : r * ξ / (1 - r) = ν * ξ / (d - ν) := by
    dsimp [r]
    field_simp <;> ring
  have hq : 0 ≤ r * ξ / (1 - r) := (div_pos (mul_pos hrpos hξ) hc).le
  have hqν : r * ξ / (1 - r) ≤ 2 * ν * ξ := by
    rw [he]
    apply (div_le_iff₀ hdνpos).mpr
    have h := mul_le_mul_of_nonneg_left hdν (mul_nonneg hν.le hξ.le)
    nlinarith
  refine ⟨hr, hq, hqν, hqν.trans ?_⟩
  nlinarith

/-- The determinant part of Proposition 2, with an explicit absolute constant.
It is pointwise, so it immediately remains true after averaging the perturbation. -/
theorem fugacity_log_det_ratio_lower {n : ℕ} (ν ξ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X Y : Herm0 n) (hX : X ∈ Gsupp n) (hY : Y ∈ Gsupp n) :
    -(128 * (n : ℝ) * ν ^ 2 * ξ ^ 2) ≤
      Real.log (1 - fugacityFamily ν ξ X).det.re -
        Real.log (1 - fugacityFamily ν ξ Y).det.re := by
  let r := ν / ((1 - 4 * ξ) * (1 + ν))
  obtain ⟨hr, hq, hqν, hq8⟩ := family_relative_parameter_bounds ν ξ hν hν1 hξ hξ32
  have hb := log_det_scalar_family_sub_lower X Y hX hY r ξ hr hq hq8
  change -(128 * (n : ℝ) * ν ^ 2 * ξ ^ 2) ≤
    Real.log (1 - (r : ℂ) • (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ))).det.re -
      Real.log (1 - (r : ℂ) • (1 + (ξ : ℂ) • (Y : Matrix (Fin n) (Fin n) ℂ))).det.re
  apply le_trans _ hb
  have hs := (sq_le_sq₀ hq (by positivity : 0 ≤ 2 * ν * ξ)).mpr hqν
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 32 * (n : ℝ) by positivity)
  nlinarith


/-- Ratio form of the determinant contribution in the paper's Equation (67). -/
theorem fugacity_log_det_quotient_lower {n : ℕ} (ν ξ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X Y : Herm0 n) (hX : X ∈ Gsupp n) (hY : Y ∈ Gsupp n) :
    -(128 * (n : ℝ) * ν ^ 2 * ξ ^ 2) ≤
      Real.log ((1 - fugacityFamily ν ξ X).det.re /
        (1 - fugacityFamily ν ξ Y).det.re) := by
  have hdx := (Complex.pos_iff.mp
    (Prop5.family_spectral_bounds ν ξ hν hν1 hξ hξ32 X hX).2.1.det_pos).1
  have hdy := (Complex.pos_iff.mp
    (Prop5.family_spectral_bounds ν ξ hν hν1 hξ hξ32 Y hY).2.1.det_pos).1
  rw [Real.log_div hdx.ne' hdy.ne']
  exact fugacity_log_det_ratio_lower ν ξ hν hν1 hξ hξ32 X Y hX hY

/-- Exponentiated, pointwise determinant likelihood lower bound. -/
theorem fugacity_det_ratio_lower {n : ℕ} (ν ξ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X Y : Herm0 n) (hX : X ∈ Gsupp n) (hY : Y ∈ Gsupp n) :
    Real.exp (-(128 * (n : ℝ) * ν ^ 2 * ξ ^ 2)) ≤
      (1 - fugacityFamily ν ξ X).det.re / (1 - fugacityFamily ν ξ Y).det.re := by
  have hdx := (Complex.pos_iff.mp
    (Prop5.family_spectral_bounds ν ξ hν hν1 hξ hξ32 X hX).2.1.det_pos).1
  have hdy := (Complex.pos_iff.mp
    (Prop5.family_spectral_bounds ν ξ hν hν1 hξ hξ32 Y hY).2.1.det_pos).1
  have h := Real.exp_le_exp.mpr
    (fugacity_log_det_quotient_lower ν ξ hν hν1 hξ hξ32 X Y hX hY)
  rwa [Real.exp_log (div_pos hdx hdy)] at h

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop1PhiFormula -/
section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace BosonicLearn.Prop5
set_option maxHeartbeats 800000

/-- The trace pairing of two Hermitian matrices is real. -/
theorem hermitian_trace_mul_selfAdjoint {n : ℕ} (X Z : Herm0 n) :
    IsSelfAdjoint (((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace) := by
  change star (((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, X.property.1, Z.property.1,
    Matrix.trace_mul_comm]

/-- The rational formula defining the relative parametrization is actually in
`Herm0`; thus its totalized fallback branch does not occur on the physical domain. -/
theorem PhiMap_formula_of_posSemidef {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (ξ : ℝ) (hξ : ξ ≠ 0) (Z : Herm0 n)
    (hS : (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)).PosSemidef)
    (hd : 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n ≠ 0) :
    let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
    let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) =
      d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) +
        CFC.sqrt S * (Z : Matrix (Fin n) (Fin n) ℂ) * CFC.sqrt S -
        e • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  classical
  let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
  let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  let T : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt S * (Z : Matrix (Fin n) (Fin n) ℂ) * CFC.sqrt S
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
  have hsqrt : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hsqrtHerm : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hTHerm : T.IsHermitian := by
    dsimp [T]
    simpa only [hsqrtHerm.eq] using
      Matrix.isHermitian_mul_mul_conjTranspose (CFC.sqrt S) Z.property.1
  have htrace := hermitian_trace_mul_selfAdjoint X Z
  have heHerm : IsSelfAdjoint e := by
    change star e = e
    simp [e, star_mul, star_div₀, htrace.star_eq, mul_comm]
  have hdHerm : IsSelfAdjoint d⁻¹ := by
    change star d⁻¹ = d⁻¹
    simp [d, star_add, star_mul, star_pow, star_div₀, htrace.star_eq, mul_comm]
  have hdform : d = 1 + (ξ : ℂ) * e := by dsimp [d, e]; ring
  have hTtrace : T.trace = (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace := by
    dsimp [T]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hsqrt]
    simp [S, Matrix.add_mul, Matrix.trace_add, Matrix.trace_smul,
      Z.property.2]
  have hnumHerm : ((X : Matrix (Fin n) (Fin n) ℂ) + T -
      e • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian :=
    (X.property.1.add hTHerm).sub (Matrix.isHermitian_one.smul heHerm)
  have hnumTrace : ((X : Matrix (Fin n) (Fin n) ℂ) + T -
      e • (1 : Matrix (Fin n) (Fin n) ℂ)).trace = 0 := by
    simp only [Matrix.trace_sub, Matrix.trace_add, X.property.2, zero_add, hTtrace,
      Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    dsimp [e]
    field_simp
    ring
  have hformula : (ξ⁻¹ : ℂ) •
      (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1) =
      d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) + T - e • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    have hprod : CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S = S + (ξ : ℂ) • T := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
        Matrix.smul_mul, hsqrt, T]
    rw [hprod]
    ext i j
    simp only [S, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    rw [hdform]
    have hden : 1 + (ξ : ℂ) * e ≠ 0 := by simpa only [← hdform] using hd
    field_simp [hden, hξc]
    ring
  have hmem : (ξ⁻¹ : ℂ) •
      (d⁻¹ • (CFC.sqrt S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * CFC.sqrt S) - 1)
      ∈ Herm0 n := by
    rw [hformula]
    exact ⟨hnumHerm.smul hdHerm, by rw [Matrix.trace_smul, hnumTrace, smul_zero]⟩
  change (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) = _
  unfold PhiMap
  dsimp only
  rw [dif_pos hmem]
  exact hformula

/-- Bounds on the real scalar denominator of the relative parametrization. -/
theorem PhiMap_denominator_bounds {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (Z : Herm0 n) (hZ : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10) :
    let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    IsSelfAdjoint d ∧ 1 - 3 * ξ^2 / 10 ≤ ‖d‖ ∧ ‖d‖ ≤ 1 + 3 * ξ^2 / 10 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hXnorm : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 := hX
  have htr : ‖((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace‖ ≤ n * (3 / 10) := by
    refine (matrix_trace_le_operator_norm _).trans ?_
    have hm := norm_mul_le (X : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin n) (Fin n) ℂ)
    have hab : ‖(X : Matrix (Fin n) (Fin n) ℂ)‖ * ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 3 * (1 / 10) := by gcongr
    nlinarith only [hm, hab, hn0]
  let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  have htrace := hermitian_trace_mul_selfAdjoint X Z
  have hdReal : IsSelfAdjoint d := by
    change star d = d
    simp [d, star_add, star_mul, star_pow, star_div₀, htrace.star_eq, mul_comm]
  have hpert : ‖d - 1‖ ≤ 3 * ξ^2 / 10 := by
    dsimp [d]
    rw [add_sub_cancel_left, norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hξ, Complex.norm_natCast]
    apply (div_le_iff₀ hn0).mpr
    nlinarith only [htr, sq_nonneg ξ, hn0]
  refine ⟨hdReal, ?_, ?_⟩
  · have hrev := norm_sub_norm_le (1 : ℂ) d
    rw [norm_one, norm_sub_rev] at hrev
    linarith
  · have hnorm := norm_add_le (d - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at hnorm
    linarith

/-- The physical parameters ensure the exact rational formula for `PhiMap`. -/
theorem PhiMap_formula {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ64 : ξ ≤ 1 / 64)
    (Z : Herm0 n) (hZ : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 / 10) :
    let S : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
    let d : ℂ := 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
    (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) =
      d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) +
        CFC.sqrt S * (Z : Matrix (Fin n) (Fin n) ℂ) * CFC.sqrt S -
        e • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  have hSp : (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    have hx := (opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) X.property.1 3 hX).2
    have he : 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ) =
        ((1 - 3 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (ξ : ℂ) • ((3 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X) := by
      push_cast
      module
    rw [he]
    exact (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith))).add
      (hx.smul (Complex.zero_le_real.mpr hξ.le))
  have hdlo := (PhiMap_denominator_bounds hn X hX ξ hξ.le Z hZ).2.1
  have hd0 : 1 + (ξ : ℂ)^2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n ≠ 0 := by
    apply norm_pos_iff.mp
    nlinarith only [hdlo, hξ, hξ64]
  exact PhiMap_formula_of_posSemidef hn X ξ hξ.ne' Z hSp hd0

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop2RelativeLikelihood -/
section
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder MatrixOrder ENNReal Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

/-- Positivity of the unscaled hard-family matrix. -/
theorem identity_add_smul_posDef {n : ℕ} (X : Herm0 n) (R ξ : ℝ)
    (hX : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ R)
    (hξ : 0 ≤ ξ) (hξR : ξ * R < 1) :
    (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
  have hx := (Prop5.opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) X.property.1 R hX).2
  have he : 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ) =
      ((1 - ξ * R : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (ξ : ℂ) • ((R : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X) := by
    push_cast
    module
  rw [he]
  exact (Matrix.PosDef.one.smul (by exact_mod_cast (sub_pos.mpr hξR))).add_posSemidef
    (hx.smul (Complex.zero_le_real.mpr hξ))

/-- The real normalizer equals the complex trace expression in `PhiMap`. -/
theorem coe_relativeNormalizer {n : ℕ} (X Z : Herm0 n) (ξ : ℝ) :
    (relativeNormalizer X ξ Z : ℂ) =
      1 + (ξ : ℂ) ^ 2 * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n := by
  have htrace := Prop5.hermitian_trace_mul_selfAdjoint X Z
  have he : ((((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace.re : ℝ) : ℂ) =
      ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace :=
    (Complex.ofReal_eq_re_of_isSelfAdjoint htrace).mp rfl
  simp only [relativeNormalizer, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, he]

/-- The exact congruence identity behind Equation (68). -/
theorem PhiMap_identity_congruence {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (Z : Herm0 n) (hZ : Z ∈ Gsupp n) :
    let S : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ))
    1 + (ξ : ℂ) • (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) =
      (((relativeNormalizer X ξ Z)⁻¹ : ℝ) : ℂ) •
        (Sᴴ * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * S) := by
  let A : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
  let S := CFC.sqrt A
  let d : ℂ := relativeNormalizer X ξ Z
  let e : ℂ := (ξ : ℂ) * ((X : Matrix (Fin n) (Fin n) ℂ) * Z).trace / n
  have hA := identity_add_smul_posDef X 3 ξ hX hξ.le (by linarith)
  have hdpos : 0 < relativeNormalizer X ξ Z := by
    have := relativeNormalizer_pos hn X hX ξ hξ hξ32 Z hZ
    linarith
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast hdpos.ne'
  have hdform : d = 1 + (ξ : ℂ) * e := by
    dsimp [d, e]
    rw [coe_relativeNormalizer]
    ring
  have hsqrt : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSH : S.IsHermitian := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hp := Prop5.PhiMap_formula_of_posSemidef hn X ξ hξ.ne' Z hA.posSemidef
    (by rw [← coe_relativeNormalizer]; exact hd)
  dsimp only at hp
  rw [← coe_relativeNormalizer] at hp
  change (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) =
    d⁻¹ • ((X : Matrix (Fin n) (Fin n) ℂ) + S * Z * S - e • 1) at hp
  change 1 + (ξ : ℂ) • (PhiMap X ξ Z : Matrix (Fin n) (Fin n) ℂ) =
    (((relativeNormalizer X ξ Z)⁻¹ : ℝ) : ℂ) • (Sᴴ * (1 + (ξ : ℂ) • Z) * S)
  rw [Complex.ofReal_inv, hSH.eq, hp]
  have hprod : S * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * S =
      A + (ξ : ℂ) • (S * Z * S) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hsqrt]
  rw [hprod]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, A]
  change (1 : Matrix (Fin n) (Fin n) ℂ) i j + (ξ : ℂ) *
    (d⁻¹ * ((X : Matrix (Fin n) (Fin n) ℂ) i j + (S * Z * S) i j - e * (1 : Matrix (Fin n) (Fin n) ℂ) i j)) =
    d⁻¹ * ((1 : Matrix (Fin n) (Fin n) ℂ) i j + (ξ : ℂ) * (X : Matrix (Fin n) (Fin n) ℂ) i j +
      (ξ : ℂ) * (S * Z * S) i j)
  field_simp
  linear_combination ((1 : Matrix (Fin n) (Fin n) ℂ) i j) * hdform

/-- The vector change in the relative parametrization is invertible on every sector. -/
theorem transformed_sector_vector_ne_zero {n : ℕ} (k : ℕ) (X : Herm0 n)
    (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0) :
    Prop5.sectorBlock k (gammaFock (CFC.sqrt
      (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)))) *ᵥ v ≠ 0 := by
  have hA := identity_add_smul_posDef X 3 ξ hX hξ.le (by linarith)
  have hS : (CFC.sqrt (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ))).PosDef := by
    apply (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).posDef_iff_isUnit.mpr
    exact (CFC.isUnit_sqrt_iff _ hA.posSemidef.nonneg).mpr hA.isUnit
  have hi := Matrix.mulVec_injective_of_isUnit (Prop5.sector_gammaFock_posDef k _ hS).isUnit
  intro hz
  apply hv
  apply hi
  simpa using hz


/-- The fugacity normalization factors out of every sector quadratic form. -/
theorem sector_fugacity_quadratic {n : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : (1 - R).PosDef)
    (v : Prop5.PhotonSector n k → ℂ) :
    Prop5.finiteQuadraticForm (Prop5.sectorBlock k (fugacityCoeff R)) v =
      (1 - R).det.re * Prop5.finiteQuadraticForm (Prop5.sectorBlock k (gammaFock R)) v := by
  have him := (Complex.pos_iff.mp hR.det_pos).2
  have he : (1 - R).det = ((1 - R).det.re : ℂ) := by
    exact Complex.ext rfl (by simpa using him.symm)
  change Prop5.finiteQuadraticForm ((1 - R).det • Prop5.sectorBlock k (gammaFock R)) v = _
  rw [he, finiteQuadraticForm_real_smul]
  simp

/-- The full one-copy likelihood factorization into determinant, scalar denominator,
and the pure perturbation sector tested on a fixed transformed vector. -/
theorem relative_sector_likelihood_ratio {n : ℕ} (hn : 1 ≤ n) (ν ξ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Ggood n) (Z : Herm0 n)
    (hZ : Z ∈ herm0Ball ⊤ 0 (1 / 10)) (k : ℕ)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0) :
    let S := CFC.sqrt (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ))
    let w := Prop5.sectorBlock k (gammaFock S) *ᵥ v
    Prop5.finiteQuadraticForm (Prop5.sectorBlock k
        (fugacityCoeff (fugacityFamily ν ξ (PhiMap X ξ Z)))) v /
      Prop5.finiteQuadraticForm (Prop5.sectorBlock k (fugacityCoeff (fugacityFamily ν ξ X))) v =
      ((1 - fugacityFamily ν ξ (PhiMap X ξ Z)).det.re / (1 - fugacityFamily ν ξ X).det.re) *
        (relativeNormalizer X ξ Z)⁻¹ ^ k *
        (Prop5.finiteQuadraticForm (Prop5.sectorBlock k (gammaFock
          (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)))) w / (∑ i, ‖w i‖ ^ 2)) := by
  let A : Matrix (Fin n) (Fin n) ℂ := 1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)
  let S := CFC.sqrt A
  let r := ν / ((1 - 4 * ξ) * (1 + ν))
  let d := relativeNormalizer X ξ Z
  have hZnorm : WHMultiplicativity.schattenNorm ⊤ (Z : Matrix (Fin n) (Fin n) ℂ) ≤ 1 / 10 := by
    simpa [herm0Ball] using hZ
  have hZsupp : Z ∈ Gsupp n := hZnorm.trans (by norm_num)
  have hXsupp : X ∈ Gsupp n := le_trans hX (by norm_num : (3 : ℝ) ≤ 4)
  have hPhi := Prop5.PhiMap_mem_Gsupp hn X hX ξ hξ hξ32 Z hZ
  have hIR := (Prop5.family_spectral_bounds ν ξ hν hν1 hξ hξ32 X hXsupp).2.1
  have hIRPhi := (Prop5.family_spectral_bounds ν ξ hν hν1 hξ hξ32 _ hPhi).2.1
  have hA := identity_add_smul_posDef X 3 ξ hX hξ.le (by linarith)
  have hSH : S.IsHermitian := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hsqrt : Sᴴ * S = A := by
    rw [hSH.eq]
    exact CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hbase : fugacityFamily ν ξ X = (r : ℂ) • (Sᴴ * S) := by rw [hsqrt]; rfl
  have hpert : fugacityFamily ν ξ (PhiMap X ξ Z) =
      ((r / d : ℝ) : ℂ) • (Sᴴ * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) * S) := by
    unfold fugacityFamily
    rw [PhiMap_identity_congruence hn X hX ξ hξ hξ32 Z hZsupp, smul_smul]
    congr 1
    simp [r, d, div_eq_mul_inv]
  have hr : r ≠ 0 := by
    dsimp [r]
    exact (div_pos hν (mul_pos (by linarith) (by linarith))).ne'
  have hd : d ≠ 0 := ne_of_gt (by
    have := relativeNormalizer_pos hn X hX ξ hξ hξ32 Z hZsupp
    change 0 < relativeNormalizer X ξ Z
    linarith)
  have hw := transformed_sector_vector_ne_zero k X hX ξ hξ hξ32 v hv
  have hratio := sector_gammaFock_relative_ratio k S
    (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) r d hr hd v hw
  change _ = _
  rw [sector_fugacity_quadratic _ _ hIRPhi, sector_fugacity_quadratic _ _ hIR,
    ← div_mul_div_comm]
  rw [hpert, hbase, hratio]
  ring


theorem vector_norm_square_pos {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → ℂ) (hv : v ≠ 0) : 0 < ∑ i, ‖v i‖ ^ 2 := by
  have h := Prop5.finiteQuadraticForm_pos (1 : Matrix I I ℂ) Matrix.PosDef.one v hv
  rwa [finiteQuadraticForm_one] at h

/-- Equation (64)–(70) as an exact logarithmic identity on finite photon sectors. -/
theorem relative_sector_log_likelihood {n : ℕ} (hn : 1 ≤ n) (ν ξ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Ggood n) (Z : Herm0 n)
    (hZ : Z ∈ herm0Ball ⊤ 0 (1 / 10)) (k : ℕ)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0) :
    let S := CFC.sqrt (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ))
    let w := Prop5.sectorBlock k (gammaFock S) *ᵥ v
    Real.log (Prop5.finiteQuadraticForm (Prop5.sectorBlock k
        (fugacityCoeff (fugacityFamily ν ξ (PhiMap X ξ Z)))) v /
      Prop5.finiteQuadraticForm (Prop5.sectorBlock k (fugacityCoeff (fugacityFamily ν ξ X))) v) =
      Real.log ((1 - fugacityFamily ν ξ (PhiMap X ξ Z)).det.re / (1 - fugacityFamily ν ξ X).det.re) +
      Real.log (Prop5.finiteQuadraticForm (Prop5.sectorBlock k (gammaFock
        (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)))) w / (∑ i, ‖w i‖ ^ 2)) -
      (k : ℝ) * Real.log (relativeNormalizer X ξ Z) := by
  classical
  dsimp only
  let w := Prop5.sectorBlock k (gammaFock (CFC.sqrt
    (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)))) *ᵥ v
  have hw : w ≠ 0 := transformed_sector_vector_ne_zero k X hX ξ hξ hξ32 v hv
  have hZnorm : WHMultiplicativity.schattenNorm ⊤ (Z : Matrix (Fin n) (Fin n) ℂ) ≤ 1 / 10 := by
    simpa [herm0Ball] using hZ
  have hZsupp : Z ∈ Gsupp n := hZnorm.trans (by norm_num)
  have hXsupp : X ∈ Gsupp n := le_trans hX (by norm_num : (3 : ℝ) ≤ 4)
  have hPhi := Prop5.PhiMap_mem_Gsupp hn X hX ξ hξ hξ32 Z hZ
  have hdx := (Complex.pos_iff.mp
    (Prop5.family_spectral_bounds ν ξ hν hν1 hξ hξ32 _ hPhi).2.1.det_pos).1
  have hdy := (Complex.pos_iff.mp
    (Prop5.family_spectral_bounds ν ξ hν hν1 hξ hξ32 X hXsupp).2.1.det_pos).1
  have hdp : 0 < relativeNormalizer X ξ Z := by
    have := relativeNormalizer_pos hn X hX ξ hξ hξ32 Z hZsupp
    linarith
  have hq : 0 < Prop5.finiteQuadraticForm (Prop5.sectorBlock k (gammaFock
      (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)))) w :=
    Prop5.finiteQuadraticForm_pos _
      (Prop5.sector_gammaFock_posDef k _ (identity_add_smul_posDef Z 4 ξ hZsupp hξ.le (by linarith)))
      w hw
  have hnorm := vector_norm_square_pos w hw
  rw [relative_sector_likelihood_ratio hn ν ξ hν hν1 hξ hξ32 X hX Z hZ k v hv,
    Real.log_mul (mul_ne_zero (div_pos hdx hdy).ne' (pow_ne_zero k (inv_pos.mpr hdp).ne'))
      (div_pos hq hnorm).ne',
    Real.log_mul (div_pos hdx hdy).ne' (pow_ne_zero k (inv_pos.mpr hdp).ne'),
    Real.log_pow, Real.log_inv]
  ring

end
end BosonicLearn.Prop2


end

/- Local helper source: Solutions.Prop2UniformPerturbation -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace BosonicLearn.Prop5

/-- Every operator-norm ball is compact in the traceless Hermitian space. -/
theorem isCompact_operator_ball (n : ℕ) (b : ℝ) :
    IsCompact (herm0Ball ⊤ (0 : Herm0 n) b) := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → ℂ))
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → ℂ))
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  apply Metric.isCompact_of_isClosed_isBounded
  · simpa [herm0Ball, WHMultiplicativity.schattenNorm] using isClosed_le hc continuous_const
  · apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max b 0, ?_⟩
    intro X hX
    have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ ≤ b := by
      simpa [herm0Ball, WHMultiplicativity.schattenNorm] using hX
    change ‖fun i j => (X : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ max b 0
    apply (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr
    intro j
    exact ((matrix_entry_le_operator_norm (X : Matrix (Fin n) (Fin n) ℂ) i j).trans hnorm).trans
      (le_max_left _ _)

/-- A positive-radius operator ball has positive Haar volume in every dimension. -/
theorem operator_ball_haar_pos (n : ℕ) (b : ℝ) (hb : 0 < b) :
    0 < (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
  have hc : Continuous fun X : Herm0 n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ := by
    apply Continuous.norm
    exact (LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)).comp
        continuous_subtype_val
  have hop : IsOpen {X : Herm0 n |
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ < b} :=
    isOpen_lt hc continuous_const
  have hne : Set.Nonempty {X : Herm0 n |
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X : Matrix (Fin n) (Fin n) ℂ)‖ < b} := by
    refine ⟨0, ?_⟩
    simpa using hb
  apply (hop.measure_pos (μ := (Measure.addHaar : Measure (Herm0 n))) hne).trans_le
  apply measure_mono
  intro X hX
  simpa [herm0Ball, WHMultiplicativity.schattenNorm] using hX.le

/-- The uniform perturbation law is a probability measure, including dimension zero. -/
theorem uniform_operator_ball_isProbability (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IsProbabilityMeasure
      (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
  exact cond_isProbabilityMeasure_of_finite (operator_ball_haar_pos n b hb).ne'
    (isCompact_operator_ball n b).measure_lt_top.ne

end BosonicLearn.Prop5

end
end

/- Local helper source: Solutions.Prop2Reduction -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix MatrixOrder ComplexOrder ENNReal

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

def uniformPerturbation (n : ℕ) (b : ℝ) : Measure (Herm0 n) :=
  cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)

instance uniformPerturbation_finite (n : ℕ) (b : ℝ) : IsFiniteMeasure (uniformPerturbation n b) :=
  Prop5.finite_cond_measure _ _

def sectorGammaValue {n : ℕ} (k : ℕ) (ξ : ℝ)
    (v : Prop5.PhotonSector n k → ℂ) (Z : Herm0 n) : ℝ :=
  Prop5.finiteQuadraticForm (Prop5.sectorBlock k
    (gammaFock (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)))) v

def sectorFamilyValue {n : ℕ} (k : ℕ) (ν ξ : ℝ)
    (v : Prop5.PhotonSector n k → ℂ) (X : Herm0 n) : ℝ :=
  Prop5.finiteQuadraticForm (Prop5.sectorBlock k (fugacityCoeff (fugacityFamily ν ξ X))) v

def sectorPureLog {n : ℕ} (k : ℕ) (ξ : ℝ)
    (v : Prop5.PhotonSector n k → ℂ) (Z : Herm0 n) : ℝ :=
  Real.log (sectorGammaValue k ξ v Z / (∑ i, ‖v i‖ ^ 2))

/-- The sole analytic sector estimate needed after the elementary reductions.
It is the conclusion of the unitary-concentration and twirling argument. -/
def UniformSectorLogLowerBound (K ξ₀ : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
    ∀ b : ℝ, 0 < b → b ≤ 1 / 10 → ∀ (k : ℕ) (v : Prop5.PhotonSector n k → ℂ),
      v ≠ 0 → -(K * ξ ^ 2 * (k : ℝ) ^ 2 / n) ≤
        ∫ Z, sectorPureLog k ξ v Z ∂uniformPerturbation n b

theorem continuous_sectorGammaValue {n : ℕ} (k : ℕ) (ξ : ℝ)
    (v : Prop5.PhotonSector n k → ℂ) : Continuous (sectorGammaValue k ξ v) := by
  classical
  unfold sectorGammaValue Prop5.finiteQuadraticForm Prop5.sectorBlock gammaFock
  fun_prop

theorem continuous_sectorFamilyValue {n : ℕ} (k : ℕ) (ν ξ : ℝ)
    (v : Prop5.PhotonSector n k → ℂ) : Continuous (sectorFamilyValue k ν ξ v) := by
  have hf (u w : Prop5.PhotonSector n k) :=
    Prop5.continuous_family_entry_family_entries ν ξ (u : Occupation (Fin n)) (w : Occupation (Fin n))
  unfold sectorFamilyValue Prop5.finiteQuadraticForm Prop5.sectorBlock
  fun_prop

theorem sectorGammaValue_pos {n : ℕ} (k : ℕ) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0) (Z : Herm0 n) (hZ : Z ∈ Gsupp n) :
    0 < sectorGammaValue k ξ v Z :=
  Prop5.finiteQuadraticForm_pos _
    (Prop5.sector_gammaFock_posDef k _ (identity_add_smul_posDef Z 4 ξ hZ hξ.le (by linarith))) v hv

theorem sectorFamilyValue_pos {n : ℕ} (k : ℕ) (ν ξ : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    0 < sectorFamilyValue k ν ξ v X :=
  Prop5.finiteQuadraticForm_pos _ (Prop5.family_sector_posDef ν ξ hν hν1 hξ hξ32 X hX k) v hv

/-- Bounded continuous functions on the support remain integrable after the relative map. -/
theorem integrable_comp_Phi_of_continuousOn {n : ℕ} (hn : 1 ≤ n)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Ggood n)
    (b : ℝ) (hb : b ≤ 1 / 10) (f : Herm0 n → ℝ)
    (hm : Measurable f) (hf : ContinuousOn f (Gsupp n)) :
    Integrable (fun Z => f (PhiMap X ξ Z)) (uniformPerturbation n b) := by
  have := Prop5.finite_cond_measure (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  obtain ⟨C, hC⟩ := (Prop5.isCompact_Gsupp n).exists_bound_of_continuousOn hf
  apply Integrable.of_bound (hm.comp (Prop5.measurable_PhiMap X ξ)).aestronglyMeasurable C
  apply ae_cond_of_forall_mem (Prop5.measurableSet_operator_ball n b)
  intro Z hZ
  apply hC
  exact Prop5.PhiMap_mem_Gsupp hn X hX ξ hξ hξ32 Z (le_trans hZ hb)

theorem integrable_log_comp_Phi {n : ℕ} (hn : 1 ≤ n)
    (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Ggood n)
    (b : ℝ) (hb : b ≤ 1 / 10) (f : Herm0 n → ℝ)
    (hf : Continuous f) (hpos : ∀ Y ∈ Gsupp n, 0 < f Y) :
    Integrable (fun Z => Real.log (f (PhiMap X ξ Z))) (uniformPerturbation n b) := by
  exact integrable_comp_Phi_of_continuousOn hn ξ hξ hξ32 X hX b hb _
    (Real.measurable_log.comp hf.measurable)
    (hf.continuousOn.log (fun Y hY => (hpos Y hY).ne'))

theorem integrable_sectorPureLog {n : ℕ} (k : ℕ) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0) (b : ℝ) (hb : b ≤ 4) :
    Integrable (sectorPureLog k ξ v) (uniformPerturbation n b) := by
  have hc := (continuous_sectorGammaValue k ξ v).div_const (∑ i, ‖v i‖ ^ 2)
  exact integrable_cond_operator_ball_of_continuousOn n b hb _
    (Real.measurable_log.comp hc.measurable)
    (hc.continuousOn.log fun Z hZ => (div_pos
      (sectorGammaValue_pos k ξ hξ hξ32 v hv Z hZ) (vector_norm_square_pos v hv)).ne')


theorem integrable_log_relativeNormalizer {n : ℕ} (hn : 1 ≤ n)
    (X : Herm0 n) (hX : X ∈ Ggood n) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (b : ℝ) (hb : b ≤ 4) :
    Integrable (fun Z => Real.log (relativeNormalizer X ξ Z)) (uniformPerturbation n b) := by
  have hc := continuous_relativeNormalizer X ξ
  exact integrable_cond_operator_ball_of_continuousOn n b hb _
    (Real.measurable_log.comp hc.measurable) (hc.continuousOn.log fun Z hZ => ne_of_gt (by
      have := relativeNormalizer_pos hn X hX ξ hξ hξ32 Z hZ
      linarith))

/-- The one-copy expected log-likelihood reduction. The perturbation-only
sector estimate is the only analytic input left. -/
theorem single_copy_log_bound_of_sector_log_bound {n : ℕ} (hn : 1 ≤ n)
    (ν ξ : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (X : Herm0 n) (hX : X ∈ Ggood n) (b : ℝ) (hb : 0 < b) (hb10 : b ≤ 1 / 10)
    (k : ℕ) (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0) (K : ℝ)
    (hsector : ∀ w : Prop5.PhotonSector n k → ℂ, w ≠ 0 →
      -(K * ξ ^ 2 * (k : ℝ) ^ 2 / n) ≤
        ∫ Z, sectorPureLog k ξ w Z ∂uniformPerturbation n b) :
    -((128 * (n : ℝ) * ν ^ 2 + K * (k : ℝ) ^ 2 / n) * ξ ^ 2) ≤
      ∫ Z, Real.log (sectorFamilyValue k ν ξ v (PhiMap X ξ Z) / sectorFamilyValue k ν ξ v X)
        ∂uniformPerturbation n b := by
  classical
  letI : IsProbabilityMeasure (uniformPerturbation n b) :=
    Prop5.uniform_operator_ball_isProbability n b hb
  let w := Prop5.sectorBlock k (gammaFock (CFC.sqrt
    (1 + (ξ : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)))) *ᵥ v
  have hw : w ≠ 0 := transformed_sector_vector_ne_zero k X hX ξ hξ hξ32 v hv
  have hXsupp : X ∈ Gsupp n := le_trans hX (by norm_num : (3 : ℝ) ≤ 4)
  let detf := fun Y : Herm0 n => (1 - fugacityFamily ν ξ Y).det.re
  have hc : Continuous detf := by unfold detf fugacityFamily; fun_prop
  have hp : ∀ Y ∈ Gsupp n, 0 < detf Y := fun Y hY =>
    (Complex.pos_iff.mp (Prop5.family_spectral_bounds ν ξ hν hν1 hξ hξ32 Y hY).2.1.det_pos).1
  have hdi := integrable_log_comp_Phi hn ξ hξ hξ32 X hX b hb10
    (fun Y => detf Y / detf X) (hc.div_const _) (fun Y hY => div_pos (hp Y hY) (hp X hXsupp))
  have hpi := integrable_sectorPureLog k ξ hξ hξ32 w hw b (by linarith)
  have hni := integrable_log_relativeNormalizer hn X hX ξ hξ hξ32 b (by linarith)
  have hEq : (fun Z => Real.log (sectorFamilyValue k ν ξ v (PhiMap X ξ Z) /
      sectorFamilyValue k ν ξ v X)) =ᵐ[uniformPerturbation n b]
      (fun Z => Real.log (detf (PhiMap X ξ Z) / detf X) + sectorPureLog k ξ w Z -
        (k : ℝ) * Real.log (relativeNormalizer X ξ Z)) := by
    apply ae_cond_of_forall_mem (Prop5.measurableSet_operator_ball n b)
    intro Z hZ
    exact relative_sector_log_likelihood hn ν ξ hν hν1 hξ hξ32 X hX Z (le_trans hZ hb10) k v hv
  have hAvg := integral_congr_ae hEq
  have hSplit := integral_sub (hdi.add hpi) (hni.const_mul (k : ℝ))
  simp only [Pi.add_apply] at hSplit
  rw [hSplit, integral_add hdi hpi, integral_const_mul] at hAvg
  have hdBound : -(128 * (n : ℝ) * ν ^ 2 * ξ ^ 2) ≤
      ∫ Z, Real.log (detf (PhiMap X ξ Z) / detf X) ∂uniformPerturbation n b := by
    calc
      _ = ∫ _Z : Herm0 n, -(128 * (n : ℝ) * ν ^ 2 * ξ ^ 2) ∂uniformPerturbation n b := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hdi (by
        apply ae_cond_of_forall_mem (Prop5.measurableSet_operator_ball n b)
        intro Z hZ
        exact fugacity_log_det_quotient_lower ν ξ hν hν1 hξ hξ32 _ X
          (Prop5.PhiMap_mem_Gsupp hn X hX ξ hξ hξ32 Z (le_trans hZ hb10)) hXsupp)
  have hpBound := hsector w hw
  have hnBound := integral_log_relativeNormalizer_nonpos hn X hX ξ hξ hξ32 b (by linarith)
  change (∫ Z, Real.log (relativeNormalizer X ξ Z) ∂uniformPerturbation n b) ≤ 0 at hnBound
  have hkBound := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hnBound
  rw [hAvg]
  calc
    _ = -(128 * (n : ℝ) * ν ^ 2 * ξ ^ 2) + -(K * ξ ^ 2 * (k : ℝ) ^ 2 / n) := by ring
    _ ≤ _ + _ := add_le_add hdBound hpBound
    _ ≤ _ := by linarith only [hkBound]


/-- Proposition 2 reduces to the dimension-scaled expected logarithm bound
for a single unnormalized photon-sector vector. -/
theorem proposition_2_of_sector_log_bound (K : ℝ) (hK : 0 < K) (ξ₀ : ℝ)
    (hξ₀ : 0 < ξ₀) (hξ₀32 : ξ₀ < 1 / 32) (hcore : UniformSectorLogLowerBound K ξ₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ X₀ ∈ Ggood n, ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∀ (N : ℕ) (k : Fin N → ℕ) (ϕ : Fin N → Occupation (Fin n) → ℂ),
        (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
        ENNReal.ofReal (Real.exp (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))) ≤
          ∫⁻ Z, ENNReal.ofReal (∏ t,
              (∑' u, ∑' v, star (ϕ t u) *
                fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) u v * ϕ t v).re /
              (∑' u, ∑' v, star (ϕ t u) * fugacityCoeff (fugacityFamily ν ξ X₀) u v * ϕ t v).re)
            ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
  classical
  refine ⟨128 + K, by linarith, ξ₀, hξ₀, hξ₀32, ?_⟩
  intro n hn ν hνlo hν1 ξ hξ hξξ X hX b hb hb10 N k φ hφsupp hφne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hν : 0 < ν := (div_pos (by norm_num) hnR).trans_le hνlo
  have hξ32 : ξ < 1 / 32 := hξξ.trans_lt hξ₀32
  have hXsupp : X ∈ Gsupp n := le_trans hX (by norm_num : (3 : ℝ) ≤ 4)
  letI : IsProbabilityMeasure (uniformPerturbation n b) :=
    Prop5.uniform_operator_ball_isProbability n b hb
  let v : (t : Fin N) → Prop5.PhotonSector n (k t) → ℂ := fun t u => φ t u
  have hv : ∀ t, v t ≠ 0 := by
    intro t ht
    apply hφne t
    funext u
    by_cases hu : ∑ i, u i = k t
    · exact congrFun ht ⟨u, hu⟩
    · exact hφsupp t u hu
  have hext : ∀ t, Prop5.extendSector (v t) = φ t := by
    intro t
    funext u
    by_cases hu : ∑ i, u i = k t
    · simp [Prop5.extendSector, hu, v]
    · simp [Prop5.extendSector, hu, hφsupp t u hu]
  have hquad (t : Fin N) (R : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) :
      (∑' u, ∑' w, star (φ t u) * R u w * φ t w).re =
        Prop5.finiteQuadraticForm (Prop5.sectorBlock (k t) R) (v t) := by
    rw [← hext t]
    exact Prop5.occupation_quadratic_form_eq_sector R (v t)
  simp_rw [hquad]
  let f : Fin N → Herm0 n → ℝ := fun t Z =>
    sectorFamilyValue (k t) ν ξ (v t) (PhiMap X ξ Z) / sectorFamilyValue (k t) ν ξ (v t) X
  let c : Fin N → ℝ := fun t => (128 + K) * ξ ^ 2 * ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)
  have hbase : ∀ t, 0 < sectorFamilyValue (k t) ν ξ (v t) X := fun t =>
    sectorFamilyValue_pos (k t) ν ξ hν hν1 hξ hξ32 (v t) (hv t) X hXsupp
  have hpos : ∀ t, ∀ᵐ Z ∂uniformPerturbation n b, 0 < f t Z := by
    intro t
    apply ae_cond_of_forall_mem (Prop5.measurableSet_operator_ball n b)
    intro Z hZ
    exact div_pos (sectorFamilyValue_pos (k t) ν ξ hν hν1 hξ hξ32 (v t) (hv t) _
      (Prop5.PhiMap_mem_Gsupp hn X hX ξ hξ hξ32 Z (le_trans hZ hb10))) (hbase t)
  have hlog : ∀ t, Integrable (fun Z => Real.log (f t Z)) (uniformPerturbation n b) := by
    intro t
    exact integrable_log_comp_Phi hn ξ hξ hξ32 X hX b hb10
      (fun Y => sectorFamilyValue (k t) ν ξ (v t) Y / sectorFamilyValue (k t) ν ξ (v t) X)
      ((continuous_sectorFamilyValue (k t) ν ξ (v t)).div_const _)
      (fun Y hY => div_pos (sectorFamilyValue_pos (k t) ν ξ hν hν1 hξ hξ32 (v t) (hv t) Y hY) (hbase t))
  have hprod : Integrable (fun Z => ∏ t, f t Z) (uniformPerturbation n b) := by
    let g : Herm0 n → ℝ := fun Y => ∏ t,
      sectorFamilyValue (k t) ν ξ (v t) Y / sectorFamilyValue (k t) ν ξ (v t) X
    have hg : Continuous g := continuous_finsetProd _ fun t _ =>
      (continuous_sectorFamilyValue (k t) ν ξ (v t)).div_const _
    exact integrable_comp_Phi_of_continuousOn hn ξ hξ hξ32 X hX b hb10 g hg.measurable hg.continuousOn
  have hlower : ∀ t, -c t ≤ ∫ Z, Real.log (f t Z) ∂uniformPerturbation n b := by
    intro t
    have hsingle := single_copy_log_bound_of_sector_log_bound hn ν ξ hν hν1 hξ hξ32
      X hX b hb hb10 (k t) (v t) (hv t) K (hcore n hn ξ hξ hξξ b hb hb10 (k t))
    apply le_trans _ hsingle
    have ha : 0 ≤ (n : ℝ) * ν ^ 2 := by positivity
    have hb' : 0 ≤ (k t : ℝ) ^ 2 / n := by positivity
    have hc : 128 * ((n : ℝ) * ν ^ 2) + K * ((k t : ℝ) ^ 2 / n) ≤
        (128 + K) * ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n) := by
      nlinarith [mul_nonneg hK.le ha]
    have hc' := neg_le_neg (mul_le_mul_of_nonneg_right hc (sq_nonneg ξ))
    dsimp only [c]
    convert hc' using 1 <;> ring
  have hj := product_expectation_lower_of_log_bounds (uniformPerturbation n b) f c hpos hlog hprod hlower
  simpa only [c, f, sectorFamilyValue, uniformPerturbation, ← Finset.mul_sum] using hj

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2UnitaryInvariance -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace BosonicLearn.Prop2

/-- A linear isometric automorphism preserves any additive Haar measure. -/
theorem linearIsometry_measurePreserving_addHaar {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : E ≃ₗᵢ[ℝ] E) (μ : Measure E) [μ.IsAddHaarMeasure] :
    MeasurePreserving e μ μ := by
  refine ⟨e.continuous.measurable, ?_⟩
  let d : ℝ := Module.finrank ℝ E
  have heq : μ = (μ.addHaarScalarFactor (Measure.hausdorffMeasure d) : ℝ≥0∞) •
      Measure.hausdorffMeasure d := Measure.isAddLeftInvariant_eq_smul μ _
  rw [heq, Measure.map_smul]
  congr 1
  exact e.toIsometryEquiv.map_hausdorffMeasure d

/-- Unitary conjugation acts isometrically on the traceless Hermitian parameter space. -/
def unitaryConjugation {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) : Herm0 n ≃ₗᵢ[ℝ] Herm0 n where
  toFun X := ⟨(U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ), by
    constructor
    · change IsSelfAdjoint _
      exact X.property.1.isSelfAdjoint.conjugate _
    · rw [Matrix.trace_mul_cycle]
      simp [mul_assoc, X.property.2]⟩
  invFun X := ⟨star (U : Matrix (Fin n) (Fin n) ℂ) * X * (U : Matrix (Fin n) (Fin n) ℂ), by
    constructor
    · change IsSelfAdjoint _
      simpa using X.property.1.isSelfAdjoint.conjugate (star (U : Matrix (Fin n) (Fin n) ℂ))
    · rw [Matrix.trace_mul_cycle]
      simp [mul_assoc, X.property.2]⟩
  left_inv X := by
    apply Subtype.ext
    change star (U : Matrix (Fin n) (Fin n) ℂ) * ((U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ)) * U = X
    simp only [← mul_assoc, Unitary.star_mul_self_of_mem U.property, one_mul]
    rw [mul_assoc, Unitary.star_mul_self_of_mem U.property, mul_one]
  right_inv X := by
    apply Subtype.ext
    change (U : Matrix (Fin n) (Fin n) ℂ) * (star (U : Matrix (Fin n) (Fin n) ℂ) * X * U) * star (U : Matrix (Fin n) (Fin n) ℂ) = X
    simp only [← mul_assoc, Unitary.mul_star_self_of_mem U.property, one_mul]
    rw [mul_assoc, Unitary.mul_star_self_of_mem U.property, mul_one]
  map_add' X Y := by ext i j; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by ext i j; simp [Matrix.mul_smul, Matrix.smul_mul]
  norm_map' X := by
    change ‖(U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ)‖ =
      ‖(X : Matrix (Fin n) (Fin n) ℂ)‖
    have h := CStarRing.norm_mul_mem_unitary ((U : Matrix (Fin n) (Fin n) ℂ) * X) (show star (U : Matrix (Fin n) (Fin n) ℂ) ∈ unitary _ from Unitary.star_mem U.property)
    rw [h]
    exact CStarRing.norm_coe_unitary_mul _ _

@[simp] theorem unitaryConjugation_apply {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Herm0 n) :
    (unitaryConjugation U X : Matrix (Fin n) (Fin n) ℂ) =
      (U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ) := rfl

theorem continuous_unitaryConjugation (n : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup (Fin n) ℂ × Herm0 n => unitaryConjugation p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : Matrix.unitaryGroup (Fin n) ℂ × Herm0 n =>
    (p.1 : Matrix (Fin n) (Fin n) ℂ) * p.2 * star (p.1 : Matrix (Fin n) (Fin n) ℂ))
  fun_prop

/-- The parameter perturbation ball is invariant under unitary conjugation. -/
theorem unitaryConjugation_preimage_ball {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (b : ℝ) :
    (unitaryConjugation U) ⁻¹' herm0Ball ⊤ 0 b = herm0Ball ⊤ 0 b := by
  ext X
  change WHMultiplicativity.schattenNorm ⊤
      ((unitaryConjugation U X - 0 : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ b ↔ _
  simp only [sub_zero]
  change ‖unitaryConjugation U X‖ ≤ b ↔ ‖X - 0‖ ≤ b
  rw [(unitaryConjugation U).norm_map, sub_zero]

/-- Uniform traceless operator-ball perturbations are invariant under unitary conjugation. -/
theorem unitaryConjugation_measurePreserving_uniform {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (b : ℝ) :
    MeasurePreserving (unitaryConjugation U)
      (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b))
      (cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
  let e := unitaryConjugation U
  have hpres := linearIsometry_measurePreserving_addHaar e (Measure.addHaar : Measure (Herm0 n))
  refine ⟨e.continuous.measurable, ?_⟩
  have hm := e.toHomeomorph.measurableEmbedding.restrict_map
    (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  change ((Measure.addHaar : Measure (Herm0 n)).map e).restrict (herm0Ball ⊤ 0 b) =
    ((Measure.addHaar : Measure (Herm0 n)).restrict (e ⁻¹' herm0Ball ⊤ 0 b)).map e at hm
  rw [hpres.map_eq, unitaryConjugation_preimage_ball] at hm
  rw [ProbabilityTheory.cond, Measure.map_smul, ← hm]

/-- Conjugating every perturbation does not change any real integral. -/
theorem integral_unitaryConjugation_uniform {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (b : ℝ) (f : Herm0 n → ℝ) :
    (∫ Z, f (unitaryConjugation U Z)
      ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) =
    ∫ Z, f Z ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
  have h := (unitaryConjugation U).toHomeomorph.measurableEmbedding.integral_map
    (μ := cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) f
  change (∫ Z, f Z ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)).map
      (unitaryConjugation U)) = _ at h
  rw [(unitaryConjugation_measurePreserving_uniform U b).map_eq] at h
  exact h.symm

/-- A lower mean bound on each unitary orbit gives the same lower bound
under the uniform perturbation law. The unitary averaging law can be any
probability measure; Haar invariance is only needed to prove the orbit bound. -/
theorem uniform_mean_lower_of_orbit_mean_lower {n : ℕ}
    [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsProbabilityMeasure μ]
    (b : ℝ) (hb : 0 < b) (f : Herm0 n → ℝ) (c : ℝ)
    (hf : Integrable (fun p : Herm0 n × Matrix.unitaryGroup (Fin n) ℂ =>
        f (unitaryConjugation p.2 p.1))
      ((cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)).prod μ))
    (hbound : ∀ Z ∈ herm0Ball ⊤ 0 b, c ≤ ∫ U, f (unitaryConjugation U Z) ∂μ) :
    c ≤ ∫ Z, f Z ∂cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b) := by
  let ν := cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)
  letI : IsProbabilityMeasure ν := Prop5.uniform_operator_ball_isProbability n b hb
  have hpoint : ∀ᵐ Z ∂ν, c ≤ ∫ U, f (unitaryConjugation U Z) ∂μ := by
    apply ae_cond_of_forall_mem (Prop5.measurableSet_operator_ball n b)
    exact hbound
  have h := integral_mono_ae (integrable_const c) hf.integral_prod_left hpoint
  rw [integral_const, probReal_univ, one_smul] at h
  apply h.trans_eq
  rw [integral_integral_swap hf]
  simp only [integral_unitaryConjugation_uniform, integral_const, probReal_univ, one_smul]

end BosonicLearn.Prop2

end
end

/- Local helper source: Solutions.Prop2SectorOrbit -/
section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

theorem measurable_sectorPureLog {n : ℕ} (k : ℕ) (ξ : ℝ)
    (v : Prop5.PhotonSector n k → ℂ) : Measurable (sectorPureLog k ξ v) :=
  Real.measurable_log.comp ((continuous_sectorGammaValue k ξ v).div_const _).measurable

theorem continuousOn_sectorPureLog {n : ℕ} (k : ℕ) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0) :
    ContinuousOn (sectorPureLog k ξ v) (Gsupp n) :=
  ((continuous_sectorGammaValue k ξ v).div_const _).continuousOn.log
    (fun Z hZ => (div_pos (sectorGammaValue_pos k ξ hξ hξ32 v hv Z hZ)
      (vector_norm_square_pos v hv)).ne')

theorem unitaryConjugation_mem_Gsupp {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (Z : Herm0 n) (hZ : Z ∈ Gsupp n) :
    unitaryConjugation U Z ∈ Gsupp n := by
  change ‖unitaryConjugation U Z‖ ≤ 4
  rw [(unitaryConjugation U).norm_map]
  exact hZ

theorem exp_sectorPureLog {n : ℕ} (k : ℕ) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0)
    (Z : Herm0 n) (hZ : Z ∈ Gsupp n) :
    Real.exp (sectorPureLog k ξ v Z) = sectorGammaValue k ξ v Z / ∑ i, ‖v i‖ ^ 2 :=
  Real.exp_log (div_pos (sectorGammaValue_pos k ξ hξ hξ32 v hv Z hZ)
    (vector_norm_square_pos v hv))

/-- A lower bound for the Haar-twirled quadratic form supplies the exponential
mean input to the logarithmic concentration inequality. -/
theorem sector_orbit_exp_mean_lower_of_quadratic_mean {n : ℕ}
    [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ))
    (k : ℕ) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0)
    (Z : Herm0 n) (hZ : Z ∈ Gsupp n)
    (hmean : (∑ i, ‖v i‖ ^ 2) ≤
      ∫ U, sectorGammaValue k ξ v (unitaryConjugation U Z) ∂μ) :
    1 ≤ ∫ U, Real.exp (sectorPureLog k ξ v (unitaryConjugation U Z)) ∂μ := by
  simp_rw [exp_sectorPureLog k ξ hξ hξ32 v hv _ (unitaryConjugation_mem_Gsupp _ Z hZ)]
  rw [integral_div]
  exact (le_div_iff₀ (vector_norm_square_pos v hv)).mpr (by simpa using hmean)

/-- Joint orbit measurability does not require regularity of a chosen averaging law. -/
theorem measurable_sectorPureLog_orbit {n : ℕ}
    [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    (k : ℕ) (ξ : ℝ) (v : Prop5.PhotonSector n k → ℂ) :
    Measurable (fun p : Herm0 n × Matrix.unitaryGroup (Fin n) ℂ =>
      sectorPureLog k ξ v (unitaryConjugation p.2 p.1)) :=
  (measurable_sectorPureLog k ξ v).comp
    ((continuous_unitaryConjugation n).comp continuous_swap).measurable

/-- All unitary conjugates stay in the same compact support, so the logarithm
is bounded uniformly in both the perturbation and the unitary. -/
theorem integrable_sectorPureLog_orbit {n : ℕ}
    [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure μ]
    (k : ℕ) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0) (b : ℝ) (hb : b ≤ 4) :
    Integrable (fun p : Herm0 n × Matrix.unitaryGroup (Fin n) ℂ =>
      sectorPureLog k ξ v (unitaryConjugation p.2 p.1))
      ((uniformPerturbation n b).prod μ) := by
  obtain ⟨C, hC⟩ := (Prop5.isCompact_Gsupp n).exists_bound_of_continuousOn
    (continuousOn_sectorPureLog k ξ hξ hξ32 v hv)
  apply Integrable.of_bound (measurable_sectorPureLog_orbit k ξ v).aestronglyMeasurable C
  have hsupport : ∀ᵐ Z ∂uniformPerturbation n b, Z ∈ Gsupp n := by
    apply ae_cond_of_forall_mem (Prop5.measurableSet_operator_ball n b)
    intro Z hZ
    exact le_trans (by simpa [herm0Ball] using hZ) hb
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsupport] with p hp
  exact hC _ (unitaryConjugation_mem_Gsupp p.2 p.1 hp)

theorem continuous_sectorPureLog_unitary {n : ℕ} (k : ℕ) (ξ : ℝ)
    (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0)
    (Z : Herm0 n) (hZ : Z ∈ Gsupp n) :
    Continuous (fun U : Matrix.unitaryGroup (Fin n) ℂ =>
      sectorPureLog k ξ v (unitaryConjugation U Z)) := by
  have hp : Continuous (fun U : Matrix.unitaryGroup (Fin n) ℂ => (U, Z)) :=
    continuous_id.prodMk continuous_const
  have hc := (continuous_unitaryConjugation n).comp hp
  exact (continuousOn_sectorPureLog k ξ hξ hξ32 v hv).comp_continuous hc
    (fun U => unitaryConjugation_mem_Gsupp U Z hZ)

/-- Orbitwise logarithmic lower bounds suffice for the remaining sector estimate. -/
theorem sector_uniform_lower_of_orbit_lower {n : ℕ}
    [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsProbabilityMeasure μ]
    (k : ℕ) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0)
    (b : ℝ) (hb : 0 < b) (hb4 : b ≤ 4) (c : ℝ)
    (hbound : ∀ Z ∈ herm0Ball ⊤ 0 b, c ≤
      ∫ U, sectorPureLog k ξ v (unitaryConjugation U Z) ∂μ) :
    c ≤ ∫ Z, sectorPureLog k ξ v Z ∂uniformPerturbation n b :=
  uniform_mean_lower_of_orbit_mean_lower μ b hb _ c
    (integrable_sectorPureLog_orbit μ k ξ hξ hξ32 v hv b hb4) hbound

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2CompleteHomogeneous -/
section
/-! The complete homogeneous symmetric polynomial is minimized, at fixed positive
mean, by the constant spectrum. The proof uses its generating-series recurrence. -/

open scoped PowerSeries Matrix ComplexOrder

namespace BosonicLearn.Prop2
noncomputable section
open Prop5

/-- Complete homogeneous polynomial as an occupation-number sum. -/
def completeHomogeneous {n : ℕ} (y : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ u : PhotonSector n k, ∏ i, y i ^ u.val i

private def geometricSeries (a : ℝ) : PowerSeries ℝ := PowerSeries.mk (fun k => a^k)

private def completeSeries {n : ℕ} (y : Fin n → ℝ) : PowerSeries ℝ :=
  ∏ i, geometricSeries (y i)

private theorem completeSeries_coeff {n : ℕ} (y : Fin n → ℝ) (k : ℕ) :
    PowerSeries.coeff k (completeSeries y) = completeHomogeneous y k := by
  classical
  rw [completeSeries, PowerSeries.coeff_prod]
  simp only [geometricSeries, PowerSeries.coeff_mk]
  unfold completeHomogeneous
  apply Finset.sum_bij (fun (u : Fin n →₀ ℕ) hu => (⟨(u : Fin n → ℕ), (Finset.mem_finsuppAntidiag.mp hu).1⟩ : PhotonSector n k))
  · simp
  · intro u hu v hv h
    apply Finsupp.ext
    intro i
    exact congrFun (congrArg Subtype.val h) i
  · intro u hu
    refine ⟨Finsupp.equivFunOnFinite.symm u.val, ?_, ?_⟩
    · simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
      simpa using u.property
    · apply Subtype.ext
      exact Finsupp.equivFunOnFinite.apply_symm_apply u.val
  · intros
    rfl

private theorem geometricSeries_derivative (a : ℝ) :
    PowerSeries.derivative ℝ (geometricSeries a) =
      PowerSeries.C a * (geometricSeries a * geometricSeries a) := by
  ext k
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul]
  simp only [geometricSeries, PowerSeries.coeff_mk]
  have heq : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, a ^ p.1 * a ^ p.2) =
      (k + 1) * a^k := by
    calc
      _ = ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal k, a^k := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
      _ = _ := by simp
  rw [heq]
  ring

private theorem completeSeries_derivative {n : ℕ} (y : Fin n → ℝ) :
    PowerSeries.derivative ℝ (completeSeries y) =
      completeSeries y * ∑ i, PowerSeries.C (y i) * geometricSeries (y i) := by
  classical
  suffices h : ∀ s : Finset (Fin n),
      PowerSeries.derivative ℝ (∏ i ∈ s, geometricSeries (y i)) =
        (∏ i ∈ s, geometricSeries (y i)) * ∑ i ∈ s, PowerSeries.C (y i) * geometricSeries (y i) from
    h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz,
      ih, geometricSeries_derivative]
    simp only [smul_eq_mul]
    ring

/-- Newton's recurrence for the complete homogeneous polynomials. -/
theorem completeHomogeneous_recurrence {n : ℕ} (y : Fin n → ℝ) (k : ℕ) :
    (k + 1) * completeHomogeneous y (k + 1) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        completeHomogeneous y p.1 * (∑ i, y i ^ (p.2 + 1)) := by
  have h := congrArg (PowerSeries.coeff k) (completeSeries_derivative y)
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h
  simp only [map_sum, PowerSeries.coeff_C_mul, geometricSeries, PowerSeries.coeff_mk,
    completeSeries_coeff] at h
  simpa only [pow_succ', mul_comm] using h

theorem completeHomogeneous_nonneg {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ i, 0 ≤ y i) (k : ℕ) : 0 ≤ completeHomogeneous y k := by
  exact Finset.sum_nonneg fun u _ => Finset.prod_nonneg fun i _ => pow_nonneg (hy i) _

@[simp] theorem completeHomogeneous_one {n : ℕ} (k : ℕ) :
    completeHomogeneous (fun _ : Fin n => (1 : ℝ)) k = Fintype.card (PhotonSector n k) := by
  simp [completeHomogeneous]

@[simp] theorem completeHomogeneous_zero {n : ℕ} (y : Fin n → ℝ) :
    completeHomogeneous y 0 = 1 := by
  rw [← completeSeries_coeff]
  simp [completeSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    geometricSeries, PowerSeries.coeff_mk]

/-- Every positive integer power sum is at least the dimension when the
nonnegative coordinates have mean one. -/
theorem powerSum_lower_of_sum_eq {n : ℕ} (hn : 1 ≤ n)
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (hsum : ∑ i, y i = n) (k : ℕ) :
    (n : ℝ) ≤ ∑ i, y i ^ k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ
    (fun _ : Fin n => (n : ℝ)⁻¹) y (by intros; positivity)
    (by simp [hn0]) (by intro i hi; exact hy i) k
  simp only [← Finset.mul_sum, hsum, inv_mul_cancel₀ hn0, one_pow] at h
  have hh := mul_le_mul_of_nonneg_left h hnpos.le
  simpa only [mul_one, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul] using hh

/-- The normalized complete homogeneous polynomial is at least one when its
nonnegative arguments have arithmetic mean one. -/
theorem completeHomogeneous_lower_of_sum_eq {n : ℕ} (hn : 1 ≤ n)
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (hsum : ∑ i, y i = n) (k : ℕ) :
    (Fintype.card (PhotonSector n k) : ℝ) ≤ completeHomogeneous y k := by
  suffices h : completeHomogeneous (fun _ : Fin n => (1 : ℝ)) k ≤ completeHomogeneous y k by
    simpa only [completeHomogeneous_one] using h
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hh : ((k : ℝ) + 1) * completeHomogeneous (fun _ : Fin n => (1 : ℝ)) (k + 1) ≤
          ((k : ℝ) + 1) * completeHomogeneous y (k + 1) := by
        rw [completeHomogeneous_recurrence, completeHomogeneous_recurrence]
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        have hp1 : p.1 < k + 1 := by omega
        have hpower : (∑ _i : Fin n, (1 : ℝ) ^ (p.2 + 1)) ≤ ∑ i, y i ^ (p.2 + 1) := by
          simpa using powerSum_lower_of_sum_eq hn y hy hsum (p.2 + 1)
        exact mul_le_mul (ih p.1 hp1) hpower (by positivity)
          (completeHomogeneous_nonneg y hy p.1)
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      nlinarith only [hh, hkpos]

/-- The sector trace of a diagonal second quantization is the complete
homogeneous polynomial of its diagonal entries. -/
theorem sector_gammaFock_diagonal_trace {n : ℕ} (y : Fin n → ℝ) (k : ℕ) :
    (sectorBlock k (gammaFock (Matrix.diagonal (fun i => (y i : ℂ))))).trace.re =
      completeHomogeneous y k := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, sectorBlock, gammaFock_diagonal_re,
    completeHomogeneous]

/-- The sector trace is invariant under one-particle cyclic products. -/
theorem sector_gammaFock_trace_comm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (sectorBlock k (gammaFock (A * B))).trace = (sectorBlock k (gammaFock (B * A))).trace := by
  rw [sector_gammaFock_mul, sector_gammaFock_mul, Matrix.trace_mul_comm]

/-- Spectral form of the complete homogeneous lower bound: a positive matrix
with trace equal to the number of modes has sector trace at least the sector dimension. -/
theorem sector_gammaFock_trace_lower {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (htrace : A.trace.re = n) (k : ℕ) :
    (Fintype.card (PhotonSector n k) : ℝ) ≤ (sectorBlock k (gammaFock A)).trace.re := by
  classical
  let U : Matrix (Fin n) (Fin n) ℂ := hA.1.eigenvectorUnitary
  let y : Fin n → ℝ := hA.1.eigenvalues
  have hU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hspec : A = U * Matrix.diagonal (fun i => (y i : ℂ)) * Uᴴ := by
    have h := hA.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [← Matrix.star_eq_conjTranspose]
    exact h
  have hsum : ∑ i, y i = n := by
    have h := congrArg Complex.re hA.1.trace_eq_sum_eigenvalues
    simp only [Complex.re_sum] at h
    exact h.symm.trans htrace
  have htr : (sectorBlock k (gammaFock A)).trace.re = completeHomogeneous y k := by
    rw [hspec, sector_gammaFock_trace_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
      sector_gammaFock_diagonal_trace]
  rw [htr]
  exact completeHomogeneous_lower_of_sum_eq hn y hA.eigenvalues_nonneg hsum k

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2GammaColumns -/
section
open scoped Matrix ComplexOrder
namespace BosonicLearn.Prop2
noncomputable section
open Prop5

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


/-- Second quantization preserves diagonal matrices. -/
theorem gammaFock_diagonal {n : ℕ} (c : Fin n → ℂ) (u v : Fin n → ℕ) :
    gammaFock (Matrix.diagonal c) u v = if u = v then ∏ i, c i ^ u i else 0 := by
  classical
  by_cases huv : u = v
  · subst v
    simp [gammaFock_diagonal_self]
  · rw [if_neg huv, gammaFock_eq, gSum_diagonal_ne c u v huv, mul_zero]

theorem sector_gammaFock_diagonal {n : ℕ} (c : Fin n → ℂ) (k : ℕ) :
    sectorBlock k (gammaFock (Matrix.diagonal c)) =
      Matrix.diagonal (fun u : PhotonSector n k => ∏ i, c i ^ u.val i) := by
  classical
  ext u v
  simp only [sectorBlock, gammaFock_diagonal, Matrix.diagonal_apply, Subtype.val_inj]

private theorem concentrated_column_unique {n : ℕ} (u : Fin n → ℕ) (j : Fin n)
    (M : Fin n → Fin n → ℕ) (hM : M ∈ gS u (Pi.single j (∑ i, u i))) :
    M = fun i l => if l = j then u i else 0 := by
  have hm := (mem_gS _ _ _).mp hM
  have hz : ∀ i l, l ≠ j → M i l = 0 := by
    intro i l hl
    have hc := hm.2 l
    simp [Pi.single_eq_of_ne hl] at hc
    exact hc i
  funext i l
  by_cases hl : l = j
  · subst l
    simp only [ite_true]
    have hr := hm.1 i
    rw [Finset.sum_eq_single j (fun l _ hl => hz i l hl) (by simp)] at hr
    exact hr
  · simp [hl, hz i l hl]

private theorem gSum_concentrated_column {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : Fin n → ℕ) (j : Fin n) :
    gSum A u (Pi.single j (∑ i, u i)) = ∏ i, A i j ^ u i / (Nat.factorial (u i) : ℂ) := by
  classical
  unfold gSum
  rw [Finset.sum_eq_single (fun i l => if l = j then u i else 0)]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.prod_eq_single j]
    · simp
    · intro l hl hlj
      simp [hlj]
    · simp
  · intro M hM hne
    exact False.elim (hne (concentrated_column_unique u j M hM))
  · intro h
    apply False.elim
    apply h
    rw [mem_gS]
    constructor
    · intro i
      simp
    · intro l
      by_cases hl : l = j
      · subst l
        simp
      · simp [hl]

/-- Every output occupation has a nonzero amplitude from a concentrated input
occupation when the corresponding one-particle column has no zero entries. -/
theorem gammaFock_concentrated_column_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : Fin n → ℕ) (j : Fin n) (hA : ∀ i, A i j ≠ 0) :
    gammaFock A u (Pi.single j (∑ i, u i)) ≠ 0 := by
  rw [gammaFock_eq, gSum_concentrated_column]
  apply mul_ne_zero
  · apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact mul_pos
      (Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos (u i))
      (Finset.prod_pos fun i _ => by positivity)
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact div_ne_zero (pow_ne_zero _ (hA i))
      (by exact_mod_cast Nat.factorial_ne_zero (u i))

/-- Second quantization of a one-particle unitary is unitary on every sector. -/
theorem sector_gammaFock_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (k : ℕ) :
    sectorBlock k (gammaFock U) ∈ Matrix.unitaryGroup (PhotonSector n k) ℂ := by
  classical
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, ← sector_gammaFock_conjTranspose,
    ← sector_gammaFock_mul]
  have h := Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.star_eq_conjTranspose] at h
  rw [h, sector_gammaFock_one]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2UnitaryColumn -/
section
open scoped Matrix ComplexOrder
namespace BosonicLearn.Prop2
noncomputable section

/-- A real rank-one Householder reflection, viewed as a complex unitary matrix. -/
theorem real_reflection_unitary {n : ℕ} (v : Fin n → ℝ)
    (hs : (∑ i, v i ^ 2) ≠ 0) :
    let s : ℝ := ∑ i, v i ^ 2
    let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => (v i : ℂ) * (v j : ℂ))
    (1 - ((2 / s : ℝ) : ℂ) • P) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  classical
  let s : ℝ := ∑ i, v i ^ 2
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => (v i : ℂ) * (v j : ℂ))
  have hP : Pᴴ = P := by
    ext i j
    simp [P, Matrix.conjTranspose_apply, mul_comm]
  have hPmul : P * P = (s : ℂ) • P := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, P, Matrix.of_apply]
    calc
      _ = ∑ l, (v i : ℂ) * (v j : ℂ) * (v l : ℂ)^2 := by
        apply Finset.sum_congr rfl
        intros
        ring
      _ = _ := by rw [← Finset.mul_sum]; simp [s]; ring
  change (1 - ((2 / s : ℝ) : ℂ) • P) ∈ Matrix.unitaryGroup (Fin n) ℂ
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose]
  have hstar : (1 - ((2 / s : ℝ) : ℂ) • P)ᴴ = 1 - ((2 / s : ℝ) : ℂ) • P := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP]
  rw [hstar]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, hPmul, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp
  ring

/-- There is a unitary matrix whose chosen column has no zero entries.
A rational Householder reflection supplies an explicit construction. -/
theorem exists_unitary_nonzero_column {n : ℕ} (j : Fin n) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ,
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ ∀ i, U i j ≠ 0 := by
  classical
  have hn : 1 ≤ n := by have := j.isLt; omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let v : Fin n → ℝ := fun i => if i = j then n + 1 else 1
  let s : ℝ := ∑ i, v i ^ 2
  have hsval : s = n + ((n : ℝ) + 1)^2 - 1 := by
    have hv : ∀ i, v i ^ 2 = 1 + if i = j then ((n : ℝ) + 1)^2 - 1 else 0 := by
      intro i
      by_cases hi : i = j <;> simp [v, hi]
    simp only [s, hv, Finset.sum_add_distrib]
    simp
    ring
  have hspos : 0 < s := by rw [hsval]; nlinarith
  have hsj : s ≠ 2 * ((n : ℝ) + 1)^2 := by rw [hsval]; nlinarith
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i l => (v i : ℂ) * (v l : ℂ))
  let U : Matrix (Fin n) (Fin n) ℂ := 1 - ((2 / s : ℝ) : ℂ) • P
  refine ⟨U, real_reflection_unitary v hspos.ne', ?_⟩
  intro i
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hnC : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by linarith)
  by_cases hi : i = j
  · subst i
    simp only [U, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply,
      smul_eq_mul, P, Matrix.of_apply]
    simp only [v, if_pos rfl]
    intro he
    have he' : (s : ℂ) = 2 * ((n : ℂ) + 1)^2 := by
      push_cast at he
      field_simp at he
      exact sub_eq_zero.mp (by simpa using he)
    apply hsj
    exact_mod_cast he'
  · simp only [U, Matrix.sub_apply, Matrix.one_apply_ne hi, Matrix.smul_apply,
      smul_eq_mul, P, Matrix.of_apply]
    simp [v, hi, hsC, hnC]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2GammaCommutant -/
section
open scoped Matrix ComplexOrder
namespace BosonicLearn.Prop2
noncomputable section
open Prop5

private theorem diagonal_unitary_of_norm_one {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) : Matrix.diagonal z ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  classical
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one using 1
  congr 1
  funext i
  simp [Pi.star_apply, Complex.mul_conj', hz i]

/-- Diagonal phase rotations separate all distinct occupation vectors. -/
theorem sector_gammaFock_commutant_offdiagonal {n k : ℕ}
    (T : Matrix (PhotonSector n k) (PhotonSector n k) ℂ)
    (hT : ∀ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ →
      Commute T (sectorBlock k (gammaFock U)))
    (u v : PhotonSector n k) (huv : u ≠ v) : T u v = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, u.val i ≠ v.val i := by
    contrapose! huv
    apply Subtype.ext
    exact funext huv
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (k + 1))
  have hζ : IsPrimitiveRoot ζ (k + 1) := by
    convert Complex.isPrimitiveRoot_exp (k + 1) (by omega) using 1
    push_cast
    rfl
  have hui : u.val i < k + 1 := by
    have h := Finset.single_le_sum (f := u.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [u.property] at h
    omega
  have hvi : v.val i < k + 1 := by
    have h := Finset.single_le_sum (f := v.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [v.property] at h
    omega
  have hp : ζ ^ u.val i ≠ ζ ^ v.val i := fun h => hi (hζ.pow_inj hui hvi h)
  let z : Fin n → ℂ := fun j => if j = i then ζ else 1
  have hz : ∀ j, ‖z j‖ = 1 := by
    intro j
    by_cases hj : j = i <;> simp [z, hj, hζ.norm'_eq_one (by omega)]
  have hphase (w : PhotonSector n k) : (∏ j, z j ^ w.val j) = ζ ^ w.val i := by
    rw [Finset.prod_eq_single i]
    · simp [z]
    · intro j hj hji
      simp [z, hji]
    · simp
  have hc := congrArg (fun A : Matrix (PhotonSector n k) (PhotonSector n k) ℂ => A u v)
    (hT (Matrix.diagonal z) (diagonal_unitary_of_norm_one z hz)).eq
  rw [sector_gammaFock_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, hphase, hphase] at hc
  have heq : (ζ ^ u.val i - ζ ^ v.val i) * T u v = 0 := by
    linear_combination -hc
  exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hp)

/-- The occupation representation of the unitary group has scalar commutant.
The proof uses phase separation and one unitary with a nonzero column. -/
theorem sector_gammaFock_commutant_scalar {n k : ℕ} (hn : 1 ≤ n)
    (T : Matrix (PhotonSector n k) (PhotonSector n k) ℂ)
    (hT : ∀ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ →
      Commute T (sectorBlock k (gammaFock U))) :
    ∃ c : ℂ, T = c • (1 : Matrix (PhotonSector n k) (PhotonSector n k) ℂ) := by
  classical
  let j : Fin n := ⟨0, by omega⟩
  let w : PhotonSector n k := ⟨Pi.single j k, by simp⟩
  have hdiag : T = Matrix.diagonal (fun u => T u u) := by
    ext u v
    by_cases huv : u = v
    · subst v
      simp
    · simp [Matrix.diagonal_apply_ne _ huv, sector_gammaFock_commutant_offdiagonal T hT u v huv]
  obtain ⟨U, hU, hcol⟩ := exists_unitary_nonzero_column j
  have hentry (u : PhotonSector n k) : sectorBlock k (gammaFock U) u w ≠ 0 := by
    have h := gammaFock_concentrated_column_ne_zero U u.val j hcol
    rw [u.property] at h
    exact h
  have hsame (u : PhotonSector n k) : T u u = T w w := by
    have hc := congrArg (fun A : Matrix (PhotonSector n k) (PhotonSector n k) ℂ => A u w)
      (hT U hU).eq
    conv_lhs at hc => rw [hdiag]
    conv_rhs at hc => rw [hdiag]
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hc
    apply mul_right_cancel₀ (hentry u)
    simpa only [mul_comm] using hc
  refine ⟨T w w, ?_⟩
  ext u v
  by_cases huv : u = v
  · subst v
    simp [hsame]
  · simp [Matrix.smul_apply, Matrix.one_apply_ne huv,
      sector_gammaFock_commutant_offdiagonal T hT u v huv]

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2UnitaryHaar -/
section
open MeasureTheory
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section

/-- The finite-dimensional unitary group carries its Borel sigma algebra. -/
instance unitaryGroupMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) := borel _

instance unitaryGroupBorelSpace (n : ℕ) :
    BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩

/-- Finite-dimensional unitary groups are compact. -/
instance unitaryGroupCompactSpace (n : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  intro U hU
  rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with h | h
  · simp only [Subsingleton.elim U 0, norm_zero, zero_le_one]
  · exact (CStarRing.norm_of_mem_unitary hU).le

/-- Probability Haar measure on the unitary group. -/
def unitaryHaar (n : ℕ) : Measure (Matrix.unitaryGroup (Fin n) ℂ) :=
  Measure.haarMeasure ⊤

deriving instance Measure.IsHaarMeasure for unitaryHaar

instance unitaryHaar_probability (n : ℕ) : IsProbabilityMeasure (unitaryHaar n) :=
  ⟨Measure.haarMeasure_self⟩

/-- Continuous functions on the unitary group are Haar integrable. -/
theorem continuous_integrable_unitaryHaar {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : Matrix.unitaryGroup (Fin n) ℂ → E) (hf : Continuous f) :
    Integrable f (unitaryHaar n) :=
  hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset isClosed_closure (by simp))

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2GammaTwirl -/
section
open MeasureTheory
open scoped Matrix ComplexOrder
namespace BosonicLearn.Prop2
noncomputable section
open Prop5
set_option maxHeartbeats 800000

/-- Entrywise integration of a finite matrix-valued function. -/
def matrixEntryIntegral {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → Matrix I I ℂ) : Matrix I I ℂ :=
  Matrix.of (fun i j => ∫ x, F x i j ∂μ)

theorem matrix_mul_entryIntegral {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (B : Matrix I I ℂ) (F : Ω → Matrix I I ℂ)
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) :
    B * matrixEntryIntegral μ F = matrixEntryIntegral μ (fun x => B * F x) := by
  ext i j
  simp only [matrixEntryIntegral, Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ (fun l _ => (hF l j).const_mul (B i l))]
  simp only [integral_const_mul]

theorem entryIntegral_mul_matrix {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (F : Ω → Matrix I I ℂ) (B : Matrix I I ℂ)
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) :
    matrixEntryIntegral μ F * B = matrixEntryIntegral μ (fun x => F x * B) := by
  ext i j
  simp only [matrixEntryIntegral, Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ (fun l _ => (hF i l).mul_const (B l j))]
  simp only [integral_mul_const]

/-- The unitary orbit after second quantization. -/
def sectorUnitaryOrbit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (PhotonSector n k) (PhotonSector n k) ℂ :=
  sectorBlock k (gammaFock ((U : Matrix (Fin n) (Fin n) ℂ) * A * star (U : Matrix (Fin n) (Fin n) ℂ)))

theorem continuous_sectorUnitaryOrbit_entry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (i j : PhotonSector n k) :
    Continuous (fun U => sectorUnitaryOrbit A k U i j) := by
  classical
  unfold sectorUnitaryOrbit sectorBlock gammaFock
  fun_prop

theorem integrable_sectorUnitaryOrbit_entry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (i j : PhotonSector n k) :
    Integrable (fun U => sectorUnitaryOrbit A k U i j) (unitaryHaar n) :=
  continuous_integrable_unitaryHaar _ (continuous_sectorUnitaryOrbit_entry A k i j)

/-- Haar twirl of the finite-sector operator. -/
def sectorHaarTwirl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Matrix (PhotonSector n k) (PhotonSector n k) ℂ :=
  matrixEntryIntegral (unitaryHaar n) (sectorUnitaryOrbit A k)

theorem sectorUnitaryOrbit_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (V U : Matrix.unitaryGroup (Fin n) ℂ) :
    sectorUnitaryOrbit A k (V * U) =
      sectorBlock k (gammaFock (V : Matrix (Fin n) (Fin n) ℂ)) * sectorUnitaryOrbit A k U *
        (sectorBlock k (gammaFock (V : Matrix (Fin n) (Fin n) ℂ)))ᴴ := by
  unfold sectorUnitaryOrbit
  simp only [Submonoid.coe_mul, star_mul, Matrix.star_eq_conjTranspose]
  simp only [sector_gammaFock_mul, sector_gammaFock_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- Haar averaging produces an operator commuting with the sector representation. -/
theorem sectorHaarTwirl_commute {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (V : Matrix.unitaryGroup (Fin n) ℂ) :
    Commute (sectorHaarTwirl A k) (sectorBlock k (gammaFock (V : Matrix (Fin n) (Fin n) ℂ))) := by
  classical
  let B := sectorBlock k (gammaFock (V : Matrix (Fin n) (Fin n) ℂ))
  have hB : B ∈ Matrix.unitaryGroup (PhotonSector n k) ℂ := sector_gammaFock_unitary _ V.property k
  have hBF (i j : PhotonSector n k) :
      Integrable (fun U => (B * sectorUnitaryOrbit A k U) i j) (unitaryHaar n) := by
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun l _ =>
      (integrable_sectorUnitaryOrbit_entry A k l j).const_mul (B i l)
  have hconj : B * sectorHaarTwirl A k * Bᴴ = sectorHaarTwirl A k := by
    rw [sectorHaarTwirl, matrix_mul_entryIntegral _ _ _ (integrable_sectorUnitaryOrbit_entry A k),
      entryIntegral_mul_matrix _ _ _ hBF]
    ext i j
    change (∫ U, (B * sectorUnitaryOrbit A k U * Bᴴ) i j ∂unitaryHaar n) = _
    have horbit (U : Matrix.unitaryGroup (Fin n) ℂ) :
        B * sectorUnitaryOrbit A k U * Bᴴ = sectorUnitaryOrbit A k (V * U) :=
      (sectorUnitaryOrbit_mul A k V U).symm
    simp_rw [horbit]
    exact integral_mul_left_eq_self (fun U => sectorUnitaryOrbit A k U i j) V
  have hstar : Bᴴ * B = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hB
  change sectorHaarTwirl A k * B = B * sectorHaarTwirl A k
  calc
    _ = (B * sectorHaarTwirl A k * Bᴴ) * B := by rw [hconj]
    _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hstar, Matrix.mul_one]

/-- Haar twirling is scalar, by the scalar commutant of the occupation representation. -/
theorem sectorHaarTwirl_scalar {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ∃ c : ℂ, sectorHaarTwirl A k = c • (1 : Matrix (PhotonSector n k) (PhotonSector n k) ℂ) := by
  apply sector_gammaFock_commutant_scalar hn
  intro V hV
  exact sectorHaarTwirl_commute A k ⟨V, hV⟩

/-- The trace of the sector operator is unchanged along each unitary orbit. -/
theorem sectorUnitaryOrbit_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (sectorUnitaryOrbit A k U).trace = (sectorBlock k (gammaFock A)).trace := by
  unfold sectorUnitaryOrbit
  rw [sector_gammaFock_trace_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]

/-- Haar twirling preserves the trace. -/
theorem sectorHaarTwirl_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (sectorHaarTwirl A k).trace = (sectorBlock k (gammaFock A)).trace := by
  change (∑ i, ∫ U, sectorUnitaryOrbit A k U i i ∂unitaryHaar n) = _
  rw [← integral_finsetSum _ (fun i _ => integrable_sectorUnitaryOrbit_entry A k i i)]
  change (∫ U, (sectorUnitaryOrbit A k U).trace ∂unitaryHaar n) = _
  simp only [sectorUnitaryOrbit_trace, integral_const, probReal_univ, one_smul]

/-- Exact Schur twirling formula for the occupation representation. -/
theorem sectorHaarTwirl_eq_scalar {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    sectorHaarTwirl A k =
      ((sectorBlock k (gammaFock A)).trace / (Fintype.card (PhotonSector n k) : ℂ)) •
        (1 : Matrix (PhotonSector n k) (PhotonSector n k) ℂ) := by
  classical
  let j : Fin n := ⟨0, by omega⟩
  let w : PhotonSector n k := ⟨Pi.single j k, by simp⟩
  let : Nonempty (PhotonSector n k) := ⟨w⟩
  have hd : (Fintype.card (PhotonSector n k) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card (PhotonSector n k) ≠ 0)
  obtain ⟨c, hc⟩ := sectorHaarTwirl_scalar hn A k
  have ht := sectorHaarTwirl_trace A k
  rw [hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at ht
  have heq : c = (sectorBlock k (gammaFock A)).trace / (Fintype.card (PhotonSector n k) : ℂ) :=
    (eq_div_iff hd).mpr ht
  rw [← heq]
  exact hc

/-- Quadratic forms commute with entrywise integration. -/
theorem integral_finiteQuadraticForm {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (F : Ω → Matrix I I ℂ) (v : I → ℂ)
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) :
    (∫ x, finiteQuadraticForm (F x) v ∂μ) = finiteQuadraticForm (matrixEntryIntegral μ F) v := by
  have hi (i j : I) : Integrable (fun x => star (v i) * F x i j * v j) μ :=
    ((hF i j).const_mul _).mul_const _
  unfold finiteQuadraticForm
  have hsum : Integrable (fun x => ∑ i : I, ∑ j : I, star (v i) * F x i j * v j) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j
  have hre : (∫ x, (∑ i : I, ∑ j : I, star (v i) * F x i j * v j).re ∂μ) =
      (∫ x, ∑ i : I, ∑ j : I, star (v i) * F x i j * v j ∂μ).re := integral_re hsum
  rw [hre]
  congr 1
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  simp only [integral_mul_const, integral_const_mul, matrixEntryIntegral, Matrix.of_apply]

/-- A scalar identity has the expected real quadratic form. -/
theorem finiteQuadraticForm_complex_smul_one {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℂ) (v : I → ℂ) :
    finiteQuadraticForm (c • (1 : Matrix I I ℂ)) v = c.re * ∑ i, ‖v i‖ ^ 2 := by
  rw [finiteQuadraticForm_eq_re_dot, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]
  simp [dotProduct, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum]

/-- Exact Haar-averaged quadratic form after second quantization. -/
theorem integral_sectorUnitaryOrbit_quadratic {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (v : PhotonSector n k → ℂ) :
    (∫ U, finiteQuadraticForm (sectorUnitaryOrbit A k U) v ∂unitaryHaar n) =
      ((sectorBlock k (gammaFock A)).trace.re / (Fintype.card (PhotonSector n k) : ℝ)) *
        ∑ i, ‖v i‖ ^ 2 := by
  rw [integral_finiteQuadraticForm _ _ _ (integrable_sectorUnitaryOrbit_entry A k)]
  change finiteQuadraticForm (sectorHaarTwirl A k) v = _
  rw [sectorHaarTwirl_eq_scalar hn, finiteQuadraticForm_complex_smul_one]
  congr 1
  exact Complex.div_ofReal_re _ (Fintype.card (PhotonSector n k))

/-- The fixed-spectrum Haar average is at least the identity when the
one-particle positive matrix has trace equal to the mode dimension. -/
theorem integral_sectorUnitaryOrbit_quadratic_lower {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (htrace : A.trace.re = n)
    (k : ℕ) (v : PhotonSector n k → ℂ) :
    (∑ i, ‖v i‖ ^ 2) ≤ ∫ U, finiteQuadraticForm (sectorUnitaryOrbit A k U) v ∂unitaryHaar n := by
  let j : Fin n := ⟨0, by omega⟩
  let w : PhotonSector n k := ⟨Pi.single j k, by simp⟩
  let : Nonempty (PhotonSector n k) := ⟨w⟩
  have hd : (0 : ℝ) < Fintype.card (PhotonSector n k) := by exact_mod_cast Fintype.card_pos
  rw [integral_sectorUnitaryOrbit_quadratic hn]
  have htrace' := sector_gammaFock_trace_lower hn A hA htrace k
  have hratio : 1 ≤ (sectorBlock k (gammaFock A)).trace.re /
      (Fintype.card (PhotonSector n k) : ℝ) := (le_div_iff₀ hd).mpr (by simpa using htrace')
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hratio (Finset.sum_nonneg fun i _ => sq_nonneg ‖v i‖)

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2GammaLipschitz -/
section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
open Prop5
noncomputable section

/-- Second quantization of a unitary is unitary on every finite photon sector. -/
theorem sector_gammaFock_mul_adjoint_unitary {n : ℕ} (k : ℕ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    sectorBlock k (gammaFock (U : Matrix (Fin n) (Fin n) ℂ)) *
      (sectorBlock k (gammaFock (U : Matrix (Fin n) (Fin n) ℂ)))ᴴ = 1 := by
  rw [← sector_gammaFock_conjTranspose, ← sector_gammaFock_mul]
  have hU := Matrix.mem_unitaryGroup_iff.mp U.property
  rw [Matrix.star_eq_conjTranspose] at hU
  rw [hU, sector_gammaFock_one]

/-- A positive one-particle spectral upper bound lifts to its `k`-th power. -/
theorem sector_gammaFock_le_scalar {n : ℕ} (k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (r : ℝ) (hr : 0 ≤ r) (hAr : ‖A‖ ≤ r) :
    sectorBlock k (gammaFock A) ≤ (r^k : ℝ) • (1 : Matrix (PhotonSector n k) (PhotonSector n k) ℂ) := by
  classical
  let U := hA.isHermitian.eigenvectorUnitary
  let V := sectorBlock k (gammaFock (U : Matrix (Fin n) (Fin n) ℂ))
  have hV : V * Vᴴ = 1 := sector_gammaFock_mul_adjoint_unitary k U
  have heigs (i : Fin n) : hA.isHermitian.eigenvalues i ≤ r := by
    have h := abs_eigenvalue_le_operator_norm A hA.isHermitian i
    have he := le_abs_self (hA.isHermitian.eigenvalues i)
    exact (he.trans h).trans hAr
  have hprod (u : PhotonSector n k) : (∏ i, hA.isHermitian.eigenvalues i ^ u.val i) ≤ r^k := by
    calc
      _ ≤ ∏ i, r ^ u.val i := Finset.prod_le_prod
        (fun i _ => pow_nonneg (hA.eigenvalues_nonneg i) _)
        (fun i _ => pow_le_pow_left₀ (hA.eigenvalues_nonneg i) (heigs i) _)
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum, u.property]
  have hdiag : (Matrix.diagonal (fun u : PhotonSector n k =>
      ((r^k - ∏ i, hA.isHermitian.eigenvalues i ^ u.val i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro u
    change (0 : ℂ) ≤ ((r^k - ∏ i, hA.isHermitian.eigenvalues i ^ u.val i : ℝ) : ℂ)
    exact_mod_cast sub_nonneg.mpr (hprod u)
  have hpos := hdiag.mul_mul_conjTranspose_same V
  rw [Matrix.le_iff]
  suffices heq : (r^k : ℝ) • (1 : Matrix (PhotonSector n k) (PhotonSector n k) ℂ) -
      sectorBlock k (gammaFock A) = V *
        Matrix.diagonal (fun u : PhotonSector n k =>
          ((r^k - ∏ i, hA.isHermitian.eigenvalues i ^ u.val i : ℝ) : ℂ)) * Vᴴ by
    rw [heq]
    exact hpos
  have hspectral := hA.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at hspectral
  change A = (U : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal
    (fun i => (hA.isHermitian.eigenvalues i : ℂ)) * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ at hspectral
  have hΓ := congrArg (fun M => sectorBlock k (gammaFock M)) hspectral
  rw [sector_gammaFock_mul, sector_gammaFock_mul, sector_gammaFock_conjTranspose,
    sector_gammaFock_diagonal] at hΓ
  rw [hΓ]
  have hId : (r^k : ℝ) • (1 : Matrix (PhotonSector n k) (PhotonSector n k) ℂ) =
      V * ((r^k : ℝ) • (1 : Matrix (PhotonSector n k) (PhotonSector n k) ℂ)) * Vᴴ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hV]
  rw [hId, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext u v
  by_cases huv : u = v
  · subst v
    simp [Matrix.diagonal_apply, Matrix.smul_apply, Complex.ofReal_sub, Complex.ofReal_prod,
      Complex.ofReal_pow]
  · simp [Matrix.diagonal_apply, huv, Matrix.smul_apply]

/-- A relative order bound between positive one-particle matrices lifts to the
corresponding power in every photon sector. -/
theorem sector_gammaFock_order_bound {n : ℕ} (k : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (hB : B.PosDef)
    (r : ℝ) (hr : 0 ≤ r) (hAB : A ≤ r • B) :
    sectorBlock k (gammaFock A) ≤ r^k • sectorBlock k (gammaFock B) := by
  classical
  let S := CFC.sqrt B
  let T := S⁻¹
  let X := T * A * T
  have hS : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hSstar : Sᴴ = S := hS.isHermitian.eq
  have hTstar : Tᴴ = T := hS.isHermitian.inv.eq
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff B hB.posSemidef.nonneg).mpr hB.isUnit
  have hST : S * T = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det S).mp hSunit)
  have hTS : T * S = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det S).mp hSunit)
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
  have hX : X.PosSemidef := by
    simpa only [hTstar] using hA.mul_mul_conjTranspose_same T
  have hTBT : T * B * T = 1 := by
    calc
      _ = (T * S) * (S * T) := by rw [← hSS]; noncomm_ring
      _ = 1 := by rw [hTS, hST, one_mul]
  have hSXS : S * X * S = A := by
    calc
      _ = (S * T) * A * (T * S) := by dsimp only [X]; noncomm_ring
      _ = A := by rw [hST, hTS, one_mul, mul_one]
  have hXle : X ≤ r • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := star_right_conjugate_le_conjugate hAB T
    rw [Matrix.star_eq_conjTranspose, hTstar, Matrix.mul_smul, Matrix.smul_mul, hTBT] at h
    exact h
  have hXnorm : ‖X‖ ≤ r := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap X hr hX.nonneg).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using hXle
  have hΓ := sector_gammaFock_le_scalar k X hX r hr hXnorm
  have h := star_right_conjugate_le_conjugate hΓ (sectorBlock k (gammaFock S))
  rw [Matrix.star_eq_conjTranspose, ← sector_gammaFock_conjTranspose, hSstar,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    ← sector_gammaFock_mul, ← sector_gammaFock_mul, hSXS,
    ← sector_gammaFock_mul, hSS] at h
  exact h

/-- Quadratic forms preserve the Loewner order. -/
theorem finiteQuadraticForm_mono {I : Type*} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (hAB : A ≤ B) (v : I → ℂ) :
    finiteQuadraticForm A v ≤ finiteQuadraticForm B v := by
  have h := finiteQuadraticForm_nonneg (B - A) (Matrix.le_iff.mp hAB) v
  simp only [finiteQuadraticForm_eq_re_dot, Matrix.sub_mulVec, dotProduct_sub,
    Complex.sub_re] at h ⊢
  linarith

/-- An additive perturbation becomes a relative order perturbation above a
strictly positive lower spectral bound. -/
theorem matrix_relative_order_of_lower_bound {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (δ : ℝ) (hδ : 0 < δ) (hδB : δ • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B) :
    A ≤ (1 + ‖A - B‖ / δ) • B := by
  have hnorm := (hA.sub hB).isSelfAdjoint.le_algebraMap_norm_self
  rw [Algebra.algebraMap_eq_smul_one] at hnorm
  have hscale := smul_le_smul_of_nonneg_left hδB (div_nonneg (norm_nonneg (A-B)) hδ.le)
  rw [smul_smul, div_mul_cancel₀ _ hδ.ne'] at hscale
  have h := sub_le_iff_le_add.mp (hnorm.trans hscale)
  simpa only [add_smul, one_smul, add_comm] using h

/-- One-sided logarithmic stability of a sector quadratic form. -/
theorem log_sector_quadratic_sub_le {n : ℕ} (k : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (δ : ℝ) (hδ : 0 < δ) (hδB : δ • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B)
    (v : PhotonSector n k → ℂ) (hv : v ≠ 0) :
    Real.log (finiteQuadraticForm (sectorBlock k (gammaFock A)) v) -
      Real.log (finiteQuadraticForm (sectorBlock k (gammaFock B)) v) ≤
        (k : ℝ) / δ * ‖A - B‖ := by
  let r := 1 + ‖A - B‖ / δ
  have hr : 0 < r := by dsimp only [r]; positivity
  have hAB := matrix_relative_order_of_lower_bound A B hA.isHermitian hB.isHermitian δ hδ hδB
  have hΓ := sector_gammaFock_order_bound k A B hA.posSemidef hB r hr.le hAB
  have hq := finiteQuadraticForm_mono hΓ v
  have heq : r^k • sectorBlock k (gammaFock B) =
      ((r^k : ℝ) : ℂ) • sectorBlock k (gammaFock B) := by
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [heq, finiteQuadraticForm_real_smul] at hq
  have hqa := finiteQuadraticForm_pos _ (sector_gammaFock_posDef k A hA) v hv
  have hqb := finiteQuadraticForm_pos _ (sector_gammaFock_posDef k B hB) v hv
  have hlog := Real.log_le_log hqa hq
  rw [Real.log_mul (pow_pos hr k).ne' hqb.ne', Real.log_pow] at hlog
  have hrlog : Real.log r ≤ ‖A - B‖ / δ := by
    have h := Real.log_le_sub_one_of_pos hr
    dsimp only [r] at h ⊢
    linarith
  have hm := mul_le_mul_of_nonneg_left hrlog (Nat.cast_nonneg k)
  calc
    _ ≤ (k : ℝ) * Real.log r := by linarith
    _ ≤ (k : ℝ) * (‖A-B‖ / δ) := hm
    _ = _ := by ring

/-- Dimension-free logarithmic Lipschitz continuity on a positive spectral cone. -/
theorem abs_log_sector_quadratic_sub_le {n : ℕ} (k : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hδA : δ • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ A)
    (hδB : δ • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B)
    (v : PhotonSector n k → ℂ) (hv : v ≠ 0) :
    |Real.log (finiteQuadraticForm (sectorBlock k (gammaFock A)) v) -
      Real.log (finiteQuadraticForm (sectorBlock k (gammaFock B)) v)| ≤
        (k : ℝ) / δ * ‖A - B‖ := by
  have hA : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp ((IsStrictlyPositive.smul hδ isStrictlyPositive_one).of_le hδA)
  have hB : B.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp ((IsStrictlyPositive.smul hδ isStrictlyPositive_one).of_le hδB)
  apply abs_le.mpr
  constructor
  · have h := log_sector_quadratic_sub_le k B A hB hA δ hδ hδA v hv
    rw [norm_sub_rev B A] at h
    linarith
  · exact log_sector_quadratic_sub_le k A B hA hB δ hδ hδB v hv

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2UnitaryLipschitz -/
section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace BosonicLearn.Prop2
open Prop5

/-- Normalizing both quadratic forms by the same vector norm does not alter
logarithmic stability. -/
theorem abs_log_normalized_sector_quadratic_sub_le {n : ℕ} (k : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hδA : δ • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ A)
    (hδB : δ • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B)
    (v : PhotonSector n k → ℂ) (hv : v ≠ 0) :
    |Real.log (finiteQuadraticForm (sectorBlock k (gammaFock A)) v / (∑ i, ‖v i‖^2)) -
      Real.log (finiteQuadraticForm (sectorBlock k (gammaFock B)) v / (∑ i, ‖v i‖^2))| ≤
        (k : ℝ) / δ * ‖A - B‖ := by
  have hA : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    ((IsStrictlyPositive.smul hδ isStrictlyPositive_one).of_le hδA)
  have hB : B.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    ((IsStrictlyPositive.smul hδ isStrictlyPositive_one).of_le hδB)
  have hqa := finiteQuadraticForm_pos _ (sector_gammaFock_posDef k A hA) v hv
  have hqb := finiteQuadraticForm_pos _ (sector_gammaFock_posDef k B hB) v hv
  have hc := finiteQuadraticForm_pos (1 : Matrix (PhotonSector n k) (PhotonSector n k) ℂ)
    Matrix.PosDef.one v hv
  rw [finiteQuadraticForm_one] at hc
  rw [Real.log_div hqa.ne' hc.ne', Real.log_div hqb.ne' hc.ne']
  simpa only [sub_sub_sub_cancel_right] using abs_log_sector_quadratic_sub_le k A B δ hδ hδA hδB v hv

/-- A Hermitian perturbation of norm at most one half preserves a uniform lower bound. -/
theorem half_le_one_add_small_hermitian {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (hnorm : ‖Y‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ 1 + Y := by
  have hlo := hY.isSelfAdjoint.neg_algebraMap_norm_le_self
  rw [Algebra.algebraMap_eq_smul_one] at hlo
  have hs : (‖Y‖ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤
      (1 / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
    smul_le_smul_of_nonneg_right hnorm zero_le_one
  calc
    _ = 1 + -((1 / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by module
    _ ≤ 1 + Y := add_le_add_right ((neg_le_neg hs).trans hlo) _

/-- Unitary conjugation is Lipschitz in its unitary argument, measured in operator norm. -/
theorem unitaryConjugation_difference_bound {n : ℕ}
    (D : Herm0 n) (hD : ‖(D : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1)
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    ‖(unitaryConjugation U D : Matrix (Fin n) (Fin n) ℂ) -
      (unitaryConjugation V D : Matrix (Fin n) (Fin n) ℂ)‖ ≤
        2 * ‖(U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)‖ := by
  let u := (U : Matrix (Fin n) (Fin n) ℂ)
  let v := (V : Matrix (Fin n) (Fin n) ℂ)
  let d := (D : Matrix (Fin n) (Fin n) ℂ)
  have heq : u * d * star u - v * d * star v =
      ((u - v) * d) * star u + v * (d * (star u - star v)) := by noncomm_ring
  change ‖u*d*star u - v*d*star v‖ ≤ 2 * ‖u-v‖
  rw [heq]
  calc
    _ ≤ ‖((u-v)*d)*star u‖ + ‖v*(d*(star u-star v))‖ := norm_add_le _ _
    _ = ‖(u-v)*d‖ + ‖d*(star u-star v)‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.property),
        CStarRing.norm_mem_unitary_mul _ V.property]
    _ ≤ ‖u-v‖ * ‖d‖ + ‖d‖ * ‖star u-star v‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖u-v‖ * 1 + 1 * ‖star u-star v‖ := by gcongr
    _ = _ := by rw [← star_sub, norm_star]; ring

/-- Every conjugated local perturbation is bounded below by one half. -/
theorem half_le_unitary_perturbation {n : ℕ}
    (D : Herm0 n) (hD : ‖(D : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (hξhalf : ξ ≤ 1 / 2)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (1 / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤
      1 + (ξ : ℂ) • (unitaryConjugation U D : Matrix (Fin n) (Fin n) ℂ) := by
  apply half_le_one_add_small_hermitian
  · exact (unitaryConjugation U D).property.1.smul (by simp [IsSelfAdjoint])
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hξ]
    change ξ * ‖unitaryConjugation U D‖ ≤ _
    rw [(unitaryConjugation U).norm_map]
    exact (mul_le_mul_of_nonneg_left hD hξ).trans (by simpa using hξhalf)

/-- The photon-sector log quadratic form has the ambient Frobenius Lipschitz
constant used in the unitary concentration step. -/
theorem sector_log_unitary_lipschitz {n : ℕ} (k : ℕ)
    (D : Herm0 n) (hD : ‖(D : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1)
    (ξ : ℝ) (hξ : 0 < ξ) (hξhalf : ξ ≤ 1 / 2)
    (v : PhotonSector n k → ℂ) (hv : v ≠ 0)
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    |Real.log (finiteQuadraticForm (sectorBlock k
        (gammaFock (1 + (ξ : ℂ) • (unitaryConjugation U D : Matrix (Fin n) (Fin n) ℂ)))) v /
          (∑ i, ‖v i‖^2)) -
      Real.log (finiteQuadraticForm (sectorBlock k
        (gammaFock (1 + (ξ : ℂ) • (unitaryConjugation V D : Matrix (Fin n) (Fin n) ℂ)))) v /
          (∑ i, ‖v i‖^2))| ≤
      (4 * k * ξ) * WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)) := by
  have h := abs_log_normalized_sector_quadratic_sub_le k
    (1 + (ξ : ℂ) • (unitaryConjugation U D : Matrix (Fin n) (Fin n) ℂ))
    (1 + (ξ : ℂ) • (unitaryConjugation V D : Matrix (Fin n) (Fin n) ℂ))
    (1 / 2) (by norm_num) (half_le_unitary_perturbation D hD ξ hξ.le hξhalf U)
      (half_le_unitary_perturbation D hD ξ hξ.le hξhalf V) v hv
  rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hξ] at h
  have hdiff := unitaryConjugation_difference_bound D hD U V
  have hF := operator_norm_le_schatten_two n
    ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ))
  rw [Matrix.l2_opNorm_toEuclideanCLM] at hF
  calc
    _ ≤ (k : ℝ) / (1 / 2) * (ξ * ‖(unitaryConjugation U D : Matrix (Fin n) (Fin n) ℂ) -
        (unitaryConjugation V D : Matrix (Fin n) (Fin n) ℂ)‖) := h
    _ ≤ (k : ℝ) / (1 / 2) * (ξ * (2 * ‖(U : Matrix (Fin n) (Fin n) ℂ) -
        (V : Matrix (Fin n) (Fin n) ℂ)‖)) := by gcongr
    _ ≤ (k : ℝ) / (1 / 2) * (ξ * (2 * WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)))) := by gcongr
    _ = _ := by ring

end BosonicLearn.Prop2

end
end

/- Local helper source: Solutions.Prop2SectorCore -/
section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

/-- The general dimension-scaled logarithmic mean consequence of Haar concentration. -/
def HaarUnitaryLogMeanBound (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ F : Matrix.unitaryGroup (Fin n) ℂ → ℝ, Continuous F →
    ∀ L : ℝ, 0 ≤ L →
    (∀ U V : Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ))) →
    Real.log (∫ U, Real.exp (F U) ∂unitaryHaar n) - C * L ^ 2 / n ≤
      ∫ U, F U ∂unitaryHaar n

theorem unitaryConjugation_identity_add {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (ξ : ℝ) (Z : Herm0 n) :
    (U : Matrix (Fin n) (Fin n) ℂ) * (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)) *
      star (U : Matrix (Fin n) (Fin n) ℂ) =
      1 + (ξ : ℂ) • (unitaryConjugation U Z : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [unitaryConjugation_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, Unitary.mul_star_self_of_mem U.property]

/-- The Haar-twirled photon-sector likelihood has exponential mean at least one. -/
theorem sectorPureLog_orbit_exp_mean_lower {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0)
    (Z : Herm0 n) (hZ : Z ∈ Gsupp n) :
    1 ≤ ∫ U, Real.exp (sectorPureLog k ξ v (unitaryConjugation U Z)) ∂unitaryHaar n := by
  apply sector_orbit_exp_mean_lower_of_quadratic_mean (unitaryHaar n) k ξ hξ hξ32 v hv Z hZ
  have hA := (identity_add_smul_posDef Z 4 ξ hZ hξ.le (by linarith)).posSemidef
  have htrace : (1 + (ξ : ℂ) • (Z : Matrix (Fin n) (Fin n) ℂ)).trace.re = n := by
    simp only [Matrix.trace_add, Matrix.trace_smul, Z.property.2, smul_zero, add_zero,
      Matrix.trace_one, Fintype.card_fin, Complex.natCast_re]
  have hm := integral_sectorUnitaryOrbit_quadratic_lower hn _ hA htrace k v
  simpa only [sectorUnitaryOrbit, unitaryConjugation_identity_add, sectorGammaValue] using hm

/-- The sole concentration input yields the required orbitwise logarithmic bound. -/
theorem sector_orbit_log_mean_lower_of_lipschitz (C : ℝ) (hmean : HaarUnitaryLogMeanBound C)
    {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) (ξ : ℝ) (hξ : 0 < ξ) (hξ32 : ξ < 1 / 32)
    (v : Prop5.PhotonSector n k → ℂ) (hv : v ≠ 0)
    (Z : Herm0 n) (hZ : Z ∈ Gsupp n)
    (hLip : ∀ U V : Matrix.unitaryGroup (Fin n) ℂ,
      |sectorPureLog k ξ v (unitaryConjugation U Z) -
        sectorPureLog k ξ v (unitaryConjugation V Z)| ≤
        (4 * (k : ℝ) * ξ) * WHMultiplicativity.schattenNorm 2
          ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ))) :
    -(16 * C * ξ ^ 2 * (k : ℝ) ^ 2 / n) ≤
      ∫ U, sectorPureLog k ξ v (unitaryConjugation U Z) ∂unitaryHaar n := by
  have h := hmean n hn
    (fun U => sectorPureLog k ξ v (unitaryConjugation U Z))
    (continuous_sectorPureLog_unitary k ξ hξ hξ32 v hv Z hZ)
    (4 * (k : ℝ) * ξ) (by positivity) hLip
  have hlog := Real.log_nonneg (sectorPureLog_orbit_exp_mean_lower hn k ξ hξ hξ32 v hv Z hZ)
  have hc : C * (4 * (k : ℝ) * ξ) ^ 2 / n =
      16 * C * ξ ^ 2 * (k : ℝ) ^ 2 / n := by ring
  rw [hc] at h
  linarith

/-- Twirling, ambient Lipschitz continuity and Haar concentration prove the
single-sector estimate uniformly over the perturbation radius. -/
theorem uniform_sector_log_lower_of_haar_logmean (C : ℝ) (hmean : HaarUnitaryLogMeanBound C) :
    UniformSectorLogLowerBound (16 * C) (1 / 64) := by
  intro n hn ξ hξ hξ64 b hb hb10 k v hv
  have hξ32 : ξ < 1 / 32 := by linarith
  apply sector_uniform_lower_of_orbit_lower (unitaryHaar n) k ξ hξ hξ32 v hv b hb
    (by linarith)
  intro Z hZ
  have hZb : WHMultiplicativity.schattenNorm ⊤ (Z : Matrix (Fin n) (Fin n) ℂ) ≤ b := by
    simpa only [herm0Ball, Set.mem_setOf_eq, sub_zero] using hZ
  have hZsupp : Z ∈ Gsupp n := hZb.trans (by linarith)
  apply sector_orbit_log_mean_lower_of_lipschitz C hmean hn k ξ hξ hξ32 v hv Z hZsupp
  have hZ1 : ‖(Z : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := hZb.trans (by linarith)
  exact sector_log_unitary_lipschitz k Z hZ1 ξ hξ (by linarith) v hv

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2Final -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

namespace BosonicLearn

/-- Proposition 2, reduced only to the general Haar-unitary concentration theorem.
All bosonic, matrix, integration and symmetry steps are proved in the imported chain. -/
theorem proposition_2_of_haar_logmean (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hmean : Prop2.HaarUnitaryLogMeanBound C₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ X₀ ∈ Ggood n, ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∀ (N : ℕ) (k : Fin N → ℕ) (ϕ : Fin N → Occupation (Fin n) → ℂ),
        (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
        ENNReal.ofReal (Real.exp (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))) ≤
          ∫⁻ Z, ENNReal.ofReal (∏ t,
              (∑' u, ∑' v, star (ϕ t u) *
                fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) u v * ϕ t v).re /
              (∑' u, ∑' v, star (ϕ t u) * fugacityCoeff (fugacityFamily ν ξ X₀) u v * ϕ t v).re)
            ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := by
  exact Prop2.proposition_2_of_sector_log_bound (16 * C₁) (by positivity)
    (1 / 64) (by norm_num) (by norm_num) (Prop2.uniform_sector_log_lower_of_haar_logmean C₁ hmean)

end BosonicLearn

end

/- Local helper source: Solutions.Prop2TailMGF -/
section
open MeasureTheory Set Filter
open scoped ENNReal
namespace BosonicLearn.Prop2
noncomputable section

/-- A Gaussian-type tail for a nonnegative variable gives a bounded exponential
moment. This is a layer-cake calculation with an explicit numerical constant. -/
theorem exp_moment_le_three_of_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ᵐ x ∂μ, 0 ≤ Y x)
    (hExp : Integrable (fun x => Real.exp (Y x)) μ)
    (htail : ∀ t : ℝ, 0 < t → μ {x | t ≤ Y x} ≤ ENNReal.ofReal (2 * Real.exp (-2 * t))) :
    (∫ x, Real.exp (Y x) ∂μ) ≤ 3 := by
  have hlayer := lintegral_comp_eq_lintegral_meas_le_mul μ hY0 hY.aemeasurable
    (fun t ht => Real.continuous_exp.intervalIntegrable 0 t)
    (ae_of_all _ fun t => (Real.exp_pos t).le)
  simp only [integral_exp, Real.exp_zero] at hlayer
  have hnegInt : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) volume := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  have hbound : (∫⁻ x, ENNReal.ofReal (Real.exp (Y x) - 1) ∂μ) ≤ 2 := by
    rw [hlayer]
    calc
      _ ≤ ∫⁻ t in Ioi 0, (2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        calc
          _ ≤ ENNReal.ofReal (2 * Real.exp (-2 * t)) * ENNReal.ofReal (Real.exp t) := by
            gcongr
            exact htail t ht
          _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            have he : 2 * Real.exp (-2 * t) * Real.exp t = 2 * Real.exp (-t) := by
              rw [mul_assoc, ← Real.exp_add]
              congr 2
              ring
            rw [he, ENNReal.ofReal_mul (by norm_num)]
            norm_num
      _ = 2 := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
        rw [← ofReal_integral_eq_lintegral_ofReal hnegInt (ae_of_all _ fun t => (Real.exp_pos _).le)]
        rw [integral_exp_neg_Ioi_zero]
        norm_num
  have hnonneg : 0 ≤ᵐ[μ] fun x => Real.exp (Y x) - 1 := by
    filter_upwards [hY0] with x hx
    exact sub_nonneg.mpr (Real.one_le_exp hx)
  have hsubint : Integrable (fun x => Real.exp (Y x) - 1) μ := hExp.sub (integrable_const 1)
  rw [← ofReal_integral_eq_lintegral_ofReal hsubint hnonneg] at hbound
  have hreal : (∫ x, Real.exp (Y x) - 1 ∂μ) ≤ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (by simpa using hbound)
  rw [integral_sub hExp (integrable_const 1)] at hreal
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hreal
  linarith

/-- A tail bound for the square gives an exponential-square moment bound. -/
theorem exp_square_moment_le_three {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (a : ℝ) (ha : 0 < a)
    (hExp : Integrable (fun x => Real.exp (X x ^ 2 / (2 * a))) μ)
    (htail : ∀ r : ℝ, 0 < r → μ {x | r ≤ X x ^ 2} ≤ ENNReal.ofReal (2 * Real.exp (-r / a))) :
    (∫ x, Real.exp (X x ^ 2 / (2 * a)) ∂μ) ≤ 3 := by
  apply exp_moment_le_three_of_exp_tail μ _ (by fun_prop)
    (ae_of_all _ fun x => div_nonneg (sq_nonneg _) (by positivity)) hExp
  intro t ht
  have hset : {x | t ≤ X x ^ 2 / (2 * a)} = {x | 2 * a * t ≤ X x ^ 2} := by
    ext x
    simp only [mem_ofPred_eq, le_div_iff₀ (show 0 < 2 * a by positivity)]
    rw [mul_comm t]
  rw [hset]
  have h := htail (2 * a * t) (by positivity)
  have he : -(2 * a * t) / a = -2 * t := by field_simp
  simpa only [he] using h

/-- Passing from absolute-value tails to square tails only changes the threshold. -/
theorem square_tail_of_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (a : ℝ)
    (htail : ∀ u : ℝ, 0 < u → μ {x | u ≤ |X x|} ≤ ENNReal.ofReal (2 * Real.exp (-u^2 / a))) :
    ∀ r : ℝ, 0 < r → μ {x | r ≤ X x ^ 2} ≤ ENNReal.ofReal (2 * Real.exp (-r / a)) := by
  intro r hr
  have hset : {x | r ≤ X x ^ 2} = {x | Real.sqrt r ≤ |X x|} := by
    ext x
    simp only [mem_ofPred_eq, Real.sqrt_le_left (abs_nonneg _), sq_abs]
  rw [hset]
  simpa only [Real.sq_sqrt hr.le] using htail (Real.sqrt r) (Real.sqrt_pos.mpr hr)

/-- Young's inequality converts an exponential-square moment into a weak
Gaussian MGF bound, with the absolute prefactor three. -/
theorem exp_moment_le_three_mul_of_square_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (a : ℝ) (ha : 0 < a)
    (hExp : Integrable (fun x => Real.exp (X x ^ 2 / (2 * a))) μ)
    (htail : ∀ r : ℝ, 0 < r → μ {x | r ≤ X x ^ 2} ≤ ENNReal.ofReal (2 * Real.exp (-r / a)))
    (t : ℝ) :
    (∫ x, Real.exp (t * X x) ∂μ) ≤ 3 * Real.exp (a * t^2 / 2) := by
  have hyoung (x : Ω) : t * X x ≤ X x ^ 2 / (2 * a) + a * t^2 / 2 := by
    apply (le_of_mul_le_mul_left ?_ (show 0 < 2 * a by positivity))
    field_simp
    nlinarith only [sq_nonneg (X x - a * t)]
  have hp (x : Ω) : Real.exp (t * X x) ≤
      Real.exp (X x ^ 2 / (2 * a)) * Real.exp (a * t^2 / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (hyoung x)
  calc
    _ ≤ ∫ x, Real.exp (X x ^ 2 / (2 * a)) * Real.exp (a * t^2 / 2) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun x => (Real.exp_pos _).le)
        (hExp.mul_const _) (ae_of_all _ hp)
    _ = (∫ x, Real.exp (X x ^ 2 / (2 * a)) ∂μ) * Real.exp (a * t^2 / 2) := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (exp_square_moment_le_three μ X hX a ha hExp htail) (Real.exp_pos _).le

/-- Weak MGF bound stated directly for absolute-value Gaussian tails. -/
theorem exp_moment_le_three_mul_of_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (a : ℝ) (ha : 0 < a)
    (hExp : Integrable (fun x => Real.exp (X x ^ 2 / (2 * a))) μ)
    (htail : ∀ u : ℝ, 0 < u → μ {x | u ≤ |X x|} ≤ ENNReal.ofReal (2 * Real.exp (-u^2 / a)))
    (t : ℝ) :
    (∫ x, Real.exp (t * X x) ∂μ) ≤ 3 * Real.exp (a * t^2 / 2) :=
  exp_moment_le_three_mul_of_square_tail μ X hX a ha hExp
    (square_tail_of_abs_tail μ X a htail) t

/-- A uniform multiplicative prefactor disappears under tensor powers. -/
theorem le_exp_of_all_pow_le_three_mul (m c : ℝ)
    (h : ∀ N : ℕ, 1 ≤ N → m^N ≤ 3 * Real.exp (N * c)) : m ≤ Real.exp c := by
  by_contra hh
  have hlt : Real.exp c < m := lt_of_not_ge hh
  have hr : 1 < m / Real.exp c := (one_lt_div (Real.exp_pos c)).mpr hlt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (3 : ℝ) hr
  have hNpos : 1 ≤ N := by
    by_contra h0
    have : N = 0 := by omega
    simp [this] at hN
  have hpow := h N hNpos
  rw [Real.exp_nat_mul] at hpow
  have hle : (m / Real.exp c)^N ≤ 3 := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos (Real.exp_pos c) N)).mpr hpow
  exact (not_lt_of_ge hle) hN

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2TensorMGF -/
section
open MeasureTheory ProbabilityTheory

namespace BosonicLearn.Prop2

/-- A bounded measurable real observable has an integrable exponential square
under any finite measure. This supplies the auxiliary moment in the tail-to-MGF
argument, without assuming a Gaussian-square moment in advance. -/
theorem integrable_exp_sq_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) (R a : ℝ) (ha : 0 < a)
    (hR : ∀ᵐ x ∂μ, |X x| ≤ R) :
    Integrable (fun x => Real.exp ((X x)^2 / (2*a))) μ := by
  apply Integrable.of_bound
    ((hX.pow_const 2 |>.div_const (2*a)).exp.aestronglyMeasurable)
    (Real.exp (R^2 / (2*a)))
  filter_upwards [hR] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hx
  nlinarith [sq_abs (X x), abs_nonneg (X x)]

/-- Finite sums of bounded measurable observables have every positive
exponential-square moment under independent copies of a probability law. -/
theorem integrable_exp_sq_sum_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) (R : ℝ) (hR : ∀ x, |X x| ≤ R)
    (K : ℕ) (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : Fin K → Ω =>
      Real.exp ((∑ i, X (x i))^2 / (2*a))) (Measure.pi (fun _ : Fin K => μ)) := by
  apply integrable_exp_sq_of_abs_le _ _
    ((Finset.measurable_sum Finset.univ fun i _ => hX.comp (measurable_pi_apply i)).aemeasurable)
    (K*R) a ha
  filter_upwards [] with x
  calc
    |∑ i, X (x i)| ≤ ∑ i, |X (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin K, R := Finset.sum_le_sum (fun i _ => hR (x i))
    _ = K*R := by simp

/-- The exponential moment of independent identically distributed summands
factors, including when the Bochner integral is defined by zero. -/
theorem integral_exp_mul_sum_eq_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (X : Ω → ℝ) (K : ℕ) (t : ℝ) :
    (∫ x : Fin K → Ω, Real.exp (t * ∑ i, X (x i))
      ∂Measure.pi (fun _ : Fin K => μ)) =
      (∫ x, Real.exp (t * X x) ∂μ)^K := by
  simp_rw [Finset.mul_sum, Real.exp_sum]
  simpa using integral_fintype_prod_eq_pow (ι := Fin K) (fun x => Real.exp (t * X x))

end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2SpectrumConcentration -/
section
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn.Prop2
noncomputable section

/-- The pre-existing unitary Haar definition uses the same normalization. -/
theorem unitaryHaar_eq_schur (n : ℕ) :
    unitaryHaar n = QAlgorithms.Schur.unitaryHaar n := by
  rfl

/-- Independent unitary samples in the existing concentration theorem. -/
theorem haarK_eq_pi (n K : ℕ) :
    SpectrumLB.haarK n K = Measure.pi (fun _ : Fin K => unitaryHaar n) := by
  rfl

/-- Cauchy--Schwarz for a sum of nonnegative distances. -/
theorem sum_le_sqrt_card_mul_sqrt_sq {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, a i ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (a i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at h
  have hc : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ ∑ i, (a i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : 0 ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (a i)^2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [Real.sq_sqrt hc, Real.sq_sqrt hs,
    sq_nonneg (∑ i, a i),
    (show 0 ≤ ∑ i, a i from Finset.sum_nonneg (fun i _ => ha i))]

/-- The Schatten 2 metric in the bosonic proof is the entrywise metric used by
`SpectrumLB.eq_7_14`. -/
theorem schatten_two_eq_entry_sqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 A = Real.sqrt (∑ x, ∑ y, ‖A x y‖^2) := by
  rw [Prop5.schatten_two_eq_sqrt]
  congr 1
  exact Finset.sum_comm

/-- Additive observables have the product Frobenius Lipschitz constant sqrt(K)L. -/
theorem sum_unitary_lipschitz {n K : ℕ}
    (F : Matrix.unitaryGroup (Fin n) ℂ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ U V : Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)))
    (U V : Fin K → Matrix.unitaryGroup (Fin n) ℂ) :
    |(∑ i, F (U i)) - ∑ i, F (V i)| ≤
      (Real.sqrt K * L) * Real.sqrt (∑ i, ∑ x, ∑ y,
        ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
          (V i : Matrix (Fin n) (Fin n) ℂ) x y‖^2) := by
  let a : Fin K → ℝ := fun i => WHMultiplicativity.schattenNorm 2
    ((U i : Matrix (Fin n) (Fin n) ℂ) - (V i : Matrix (Fin n) (Fin n) ℂ))
  have ha (i) : 0 ≤ a i := by
    dsimp [a]
    rw [schatten_two_eq_entry_sqrt]
    exact Real.sqrt_nonneg _
  have hs (i) : (a i)^2 = ∑ x, ∑ y,
      ‖(U i : Matrix (Fin n) (Fin n) ℂ) x y -
        (V i : Matrix (Fin n) (Fin n) ℂ) x y‖^2 := by
    dsimp [a]
    rw [schatten_two_eq_entry_sqrt, Real.sq_sqrt]
    · rfl
    · positivity
  calc
    _ = |∑ i, (F (U i) - F (V i))| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |F (U i) - F (V i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, L * a i := Finset.sum_le_sum (fun i _ => hLip (U i) (V i))
    _ = L * ∑ i, a i := (Finset.mul_sum _ _ _).symm
    _ ≤ L * (Real.sqrt (Fintype.card (Fin K)) * Real.sqrt (∑ i, (a i)^2)) := by
      gcongr
      exact sum_le_sqrt_card_mul_sqrt_sq a ha
    _ = _ := by simp_rw [Fintype.card_fin, hs]; ring

/-- The expectation of an additive observable under independent Haar samples. -/
theorem integral_sum_unitary {n K : ℕ}
    (F : Matrix.unitaryGroup (Fin n) ℂ → ℝ) (hF : Continuous F) :
    (∫ U, ∑ i : Fin K, F (U i) ∂SpectrumLB.haarK n K) =
      K * ∫ U, F U ∂unitaryHaar n := by
  rw [haarK_eq_pi, integral_finsetSum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin K => unitaryHaar n)
        hF.aestronglyMeasurable]
    simp
  · intro i _
    exact integrable_comp_eval (continuous_integrable_unitaryHaar F hF)

/-- The exponential moment of a sum factors exactly. -/
theorem integral_exp_sum_unitary {n K : ℕ}
    (F : Matrix.unitaryGroup (Fin n) ℂ → ℝ) :
    (∫ U, Real.exp (∑ i : Fin K, F (U i)) ∂SpectrumLB.haarK n K) =
      (∫ U, Real.exp (F U) ∂unitaryHaar n)^K := by
  rw [haarK_eq_pi]
  simp_rw [Real.exp_sum]
  simpa using integral_fintype_prod_eq_pow (ι := Fin K) (fun U => Real.exp (F U))

/-- Product concentration for centered additive observables, in variance-proxy form. -/
theorem centered_sum_unitary_tail {n K : ℕ} (hn : 4 ≤ n) (hK : 1 ≤ K)
    (F : Matrix.unitaryGroup (Fin n) ℂ → ℝ) (hF : Continuous F)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V : Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)))
    (u : ℝ) (hu : 0 ≤ u) :
    (SpectrumLB.haarK n K).real
      {U | u ≤ |∑ i : Fin K, (F (U i) - ∫ V, F V ∂unitaryHaar n)|} ≤
      2 * Real.exp (-u^2 / ((K : ℝ) * (24 * L^2 / ((n : ℝ) - 2)))) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hn0 : (0 : ℝ) < (n : ℝ) - 2 := by
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h := SpectrumLB.eq_7_14 n K (Real.sqrt K * L) (by positivity)
    (fun U => ∑ i, F (U i)) (sum_unitary_lipschitz F L hL.le hLip) u hu
  rw [integral_sum_unitary F hF] at h
  have heq (U : Fin K → Matrix.unitaryGroup (Fin n) ℂ) :
      (∑ i, F (U i)) - K * ∫ V, F V ∂unitaryHaar n =
        ∑ i, (F (U i) - ∫ V, F V ∂unitaryHaar n) := by
    simp [Finset.sum_sub_distrib]
  simp_rw [heq] at h
  have hexp : -(((n : ℝ) - 2) * u^2) / (24 * (Real.sqrt K * L)^2) =
      -u^2 / ((K : ℝ) * (24 * L^2 / ((n : ℝ) - 2))) := by
    rw [mul_pow, Real.sq_sqrt hK0.le]
    field_simp
  rw [hexp] at h
  have ht := ENNReal.toReal_mono (by finiteness) h
  have hpos : 0 ≤ 2 * Real.exp (-u^2 / ((K : ℝ) * (24 * L^2 / ((n : ℝ) - 2)))) := by positivity
  simpa only [measureReal_def, ENNReal.toReal_ofReal hpos] using ht

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop5GaussianDensity -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5

/-- An integrable product density is the density of the product measures. -/
theorem pi_withDensity_ofReal {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod_dep (fun i => (hf i).restrict))
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => hn i (x i))))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hn i))

/-- Transporting a density through a measurable equivalence composes it with the inverse. -/
theorem map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (e : E ≃ᵐ F) (f : E → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator hs]
  rw [lintegral_map (show Measurable (s.indicator (fun y => f (e.symm y))) from
    (hf.comp e.symm.measurable).indicator hs) e.measurable]
  rw [← lintegral_indicator (e.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s <;> simp [Set.indicator, hx]

/-- Independent real Gaussian coordinates have the product of their scalar densities. -/
theorem pi_gaussian_density {ι : Type*} [Fintype ι] (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : ι => gaussianReal 0 v) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 v (x i))) := by
  simp_rw [gaussianReal_of_var_ne_zero _ hv]
  exact pi_withDensity_ofReal (fun _ => volume) (fun _ => gaussianPDFReal 0 v)
    (fun _ => integrable_gaussianPDFReal 0 v) (fun _ => gaussianPDFReal_nonneg 0 v)

theorem prod_gaussianPDFReal {ι : Type*} [Fintype ι] (v : ℝ≥0) (x : ι → ℝ) :
    (∏ i, gaussianPDFReal 0 v (x i)) =
      (Real.sqrt (2 * Real.pi * v))⁻¹ ^ Fintype.card ι *
        Real.exp (-(∑ i, x i ^ 2) / (2 * v)) := by
  simp only [gaussianPDFReal, sub_zero, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ← Real.exp_sum, ← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- A nonzero finite constant multiplying a measure does not change its normalization. -/
theorem cond_smul_univ {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ProbabilityTheory.cond (c • μ) Set.univ = ProbabilityTheory.cond μ Set.univ := by
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply,
    smul_eq_mul, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c⁻¹,
    ENNReal.inv_mul_cancel_right hc0 hct]

theorem map_cond_univ {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (f : E → F) (hf : Measurable f) :
    (ProbabilityTheory.cond μ Set.univ).map f =
      ProbabilityTheory.cond (μ.map f) Set.univ := by
  simp only [ProbabilityTheory.cond, Measure.restrict_univ, Measure.map_smul,
    Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

/-- A product of centered real Gaussians is the normalized radial Gaussian density. -/
theorem pi_gaussian_eq_cond_radial {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : ι => gaussianReal 0 v) =
      ProbabilityTheory.cond
        ((volume : Measure (ι → ℝ)).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v))))) Set.univ := by
  let c : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ ^ Fintype.card ι
  have hc : 0 < c := by
    dsimp [c]
    apply pow_pos
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
  have heq : Measure.pi (fun _ : ι => gaussianReal 0 v) =
      ENNReal.ofReal c • (volume : Measure (ι → ℝ)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v)))) := by
    rw [pi_gaussian_density v hv]
    simp_rw [prod_gaussianPDFReal]
    change (volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (c * Real.exp (-(∑ i, x i ^ 2) / (2 * v)))) = _
    simp_rw [ENNReal.ofReal_mul hc.le]
    exact withDensity_smul _ (by fun_prop)
  calc
    _ = ProbabilityTheory.cond (Measure.pi (fun _ : ι => gaussianReal 0 v)) Set.univ :=
      (ProbabilityTheory.cond_univ _).symm
    _ = _ := by
      rw [heq]
      exact cond_smul_univ _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top

/-- Normalizing a density makes it independent of the normalization of additive Haar measure. -/
theorem cond_withDensity_haar_eq {E : Type*} [AddCommGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [LocallyCompactSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] (f : E → ℝ≥0∞) :
    ProbabilityTheory.cond (μ.withDensity f) Set.univ =
      ProbabilityTheory.cond (ν.withDensity f) Set.univ := by
  have heq : μ = (Measure.addHaarScalarFactor μ ν : ℝ≥0∞) • ν :=
    Measure.isAddLeftInvariant_eq_smul μ ν
  rw [heq, withDensity_smul_measure]
  exact cond_smul_univ _ _
    (by exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne')
    ENNReal.coe_ne_top

/-- A quadratic form represented by orthonormal real coordinates has its expected Gaussian
density with respect to any additive Haar measure. No determinant normalization is needed. -/
theorem map_pi_gaussian_eq_cond_quadratic {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : (ι → ℝ) ≃L[ℝ] E)
    (Q : E → ℝ) (he : ∀ x, Q (e x) = ∑ i, x i ^ 2)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).map e =
      ProbabilityTheory.cond (μ.withDensity
        (fun y => ENNReal.ofReal (Real.exp (-Q y / (2 * v))))) Set.univ := by
  rw [pi_gaussian_eq_cond_radial v hv, map_cond_univ _ _ e.continuous.measurable]
  let em := e.toHomeomorph.toMeasurableEquiv
  have hmap := map_withDensity_equiv (volume : Measure (ι → ℝ)) em
    (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v)))) (by fun_prop)
  change (Measure.map e ((volume : Measure (ι → ℝ)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-(∑ i, x i ^ 2) / (2 * v)))))) =
      (Measure.map e volume).withDensity
        (fun y => ENNReal.ofReal (Real.exp (-(∑ i, (e.symm y) i ^ 2) / (2 * v)))) at hmap
  rw [hmap]
  have he' : ∀ y, (∑ i, (e.symm y) i ^ 2) = Q y := by
    intro y
    simpa only [e.apply_symm_apply] using (he (e.symm y)).symm
  simp_rw [he']
  exact cond_withDensity_haar_eq _ μ _

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop5GUECoordinates -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace BosonicLearn.Prop5

noncomputable section

/-- Flattening matrix entries gives the usual Frobenius Hilbert space. -/
def frobeniusMatrixEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  invFun x := fun i j => x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (PiLp.continuous_toLp _ _).comp (by fun_prop)
  continuous_invFun := by fun_prop

def FrobHerm0 (n : ℕ) : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
  (Herm0 n).map (frobeniusMatrixEquiv n).toLinearMap

def frobeniusHerm0Equiv (n : ℕ) : Herm0 n ≃L[ℝ] FrobHerm0 n :=
  (frobeniusMatrixEquiv n).submoduleMap (Herm0 n)

theorem norm_frobeniusMatrixEquiv (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖frobeniusMatrixEquiv n A‖ = WHMultiplicativity.schattenNorm 2 A := by
  rw [schatten_two_eq_sqrt, ← Real.sqrt_sq (norm_nonneg (frobeniusMatrixEquiv n A)),
    EuclideanSpace.norm_sq_eq]
  congr 1
  change (∑ ij : Fin n × Fin n, ‖A ij.1 ij.2‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Orthonormal real coordinates of the traceless Hermitian Frobenius space. -/
noncomputable def gueCoordinates (n : ℕ) :
    (Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) ≃L[ℝ] Herm0 n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => ℝ)).symm.trans
    ((stdOrthonormalBasis ℝ (FrobHerm0 n)).repr.symm.toContinuousLinearEquiv.trans
      (frobeniusHerm0Equiv n).symm)

theorem schatten_two_gueCoordinates (n : ℕ)
    (x : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) :
    WHMultiplicativity.schattenNorm 2
      (gueCoordinates n x : Matrix (Fin n) (Fin n) ℂ) ^ 2 = ∑ i, x i ^ 2 := by
  rw [← norm_frobeniusMatrixEquiv]
  change ‖((frobeniusHerm0Equiv n) (gueCoordinates n x) : FrobHerm0 n)‖ ^ 2 = _
  simp only [gueCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change ‖(stdOrthonormalBasis ℝ (FrobHerm0 n)).repr.symm (WithLp.toLp 2 x)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq]
  simp

/-- The density-defined traceless GUE is exactly the orthonormal-coordinate Gaussian law. -/
theorem map_gaussian_gueCoordinates (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) =>
      gaussianReal 0 (2 / (n : ℝ≥0)))).map (gueCoordinates n) = tracelessGUE n := by
  have : SecondCountableTopology (Herm0 n) :=
    @TopologicalSpace.Subtype.secondCountableTopology (Fin n → Fin n → ℂ) _
      (fun X => X ∈ Herm0 n) inferInstance
  have hv : (2 / (n : ℝ≥0)) ≠ 0 := div_ne_zero (by norm_num) (by exact_mod_cast hn.ne')
  rw [map_pi_gaussian_eq_cond_quadratic (Measure.addHaar : Measure (Herm0 n))
    (gueCoordinates n)
    (fun X => WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)
    (schatten_two_gueCoordinates n) _ hv]
  unfold tracelessGUE tracelessGUEWeight
  congr 2
  funext X
  congr 2
  simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
  field_simp
  ring

def gueStandardMap (n : ℕ) :
    (Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) →L[ℝ] Herm0 n :=
  (gueCoordinates n).toContinuousLinearMap.comp
    ((Real.sqrt (2 / (n : ℝ))) • ContinuousLinearMap.id ℝ _)

theorem map_standardGaussian_gueStandardMap (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (gueStandardMap n) = tracelessGUE n := by
  have hscale : (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (fun x => Real.sqrt (2 / (n : ℝ)) • x) =
      Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 (2 / (n : ℝ≥0))) := by
    change (Measure.pi (fun _ : Fin (Module.finrank ℝ (FrobHerm0 n)) => gaussianReal 0 1)).map
      (fun x i => Real.sqrt (2 / (n : ℝ)) * x i) = _
    rw [Measure.pi_map_pi (f := fun _ z => Real.sqrt (2 / (n : ℝ)) * z)
      (fun _ => by fun_prop)]
    congr 1
    funext i
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mk, NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
    exact Real.sq_sqrt (by positivity)
  have hcomp : (gueStandardMap n : _ → _) =
      (gueCoordinates n) ∘ (fun x => Real.sqrt (2 / (n : ℝ)) • x) := rfl
  rw [hcomp, ← Measure.map_map (gueCoordinates n).continuous.measurable (by fun_prop), hscale]
  exact map_gaussian_gueCoordinates n hn

theorem schatten_two_gueStandardMap (n : ℕ)
    (x : Fin (Module.finrank ℝ (FrobHerm0 n)) → ℝ) :
    WHMultiplicativity.schattenNorm 2
      (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) =
      Real.sqrt (2 / (n : ℝ)) * Real.sqrt (∑ i, x i ^ 2) := by
  have hsq := schatten_two_gueCoordinates n (Real.sqrt (2 / (n : ℝ)) • x)
  change WHMultiplicativity.schattenNorm 2 (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) ^ 2 = _ at hsq
  have hnrm : 0 ≤ WHMultiplicativity.schattenNorm 2 (gueStandardMap n x : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← norm_frobeniusMatrixEquiv]
    exact norm_nonneg _
  rw [← Real.sqrt_sq hnrm, hsq]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.sqrt_nonneg _)]

end
end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop2HaarSmallDimension -/
section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn.Prop5

/-- Hoeffding's lemma bounds the log exponential mean by the mean and the square
of the width of an almost-sure range. -/
theorem logmean_le_mean_add_range_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : AEMeasurable F μ)
    (a b : ℝ) (hbound : ∀ᵐ x ∂μ, F x ∈ Set.Icc a b) :
    Real.log (∫ x, Real.exp (F x) ∂μ) ≤ (∫ x, F x ∂μ) + (b-a)^2/8 := by
  have h := (hasSubgaussianMGF_of_mem_Icc hF hbound).cgf_le 1
  have hint : Integrable (fun x => Real.exp (1 * F x)) μ :=
    integrable_exp_mul_of_mem_Icc hF hbound
  have hm : 0 < mgf F μ 1 := mgf_pos hint
  have hshift : cgf (fun x => F x - ∫ y, F y ∂μ) μ 1 =
      Real.log (∫ x, Real.exp (F x) ∂μ) - ∫ y, F y ∂μ := by
    unfold cgf
    simp only [sub_eq_add_neg]
    rw [mgf_add_const, Real.log_mul hm.ne' (Real.exp_pos _).ne', Real.log_exp]
    simp [mgf, sub_eq_add_neg]
  rw [hshift] at h
  have hconst : (((‖b-a‖₊ / 2)^2 : NNReal) : ℝ) * (1 : ℝ)^2 / 2 = (b-a)^2/8 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, one_pow, mul_one, div_pow]
    rw [sq_abs]
    ring
  rw [hconst] at h
  linarith

/-- The Frobenius norm of a unitary matrix is the square root of its dimension. -/
theorem schatten_two_unitary (n : ℕ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2 (U : Matrix (Fin n) (Fin n) ℂ) = Real.sqrt n := by
  have hn : 0 ≤ WHMultiplicativity.schattenNorm 2 (U : Matrix (Fin n) (Fin n) ℂ) := by
    rw [schatten_two_eq_sqrt]
    positivity
  rw [← Real.sqrt_sq hn, schatten_two_sq_eq_trace]
  have hU := Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [Matrix.star_eq_conjTranspose] at hU
  rw [hU]
  simp

/-- The ambient Frobenius diameter of the unitary group is at most `2*sqrt n`. -/
theorem schatten_two_unitary_sub_le (n : ℕ)
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    WHMultiplicativity.schattenNorm 2
      ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ)) ≤ 2 * Real.sqrt n := by
  rw [← norm_frobeniusMatrixEquiv, map_sub]
  calc
    _ ≤ ‖frobeniusMatrixEquiv n (U : Matrix (Fin n) (Fin n) ℂ)‖ +
        ‖frobeniusMatrixEquiv n (V : Matrix (Fin n) (Fin n) ℂ)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_frobeniusMatrixEquiv, norm_frobeniusMatrixEquiv,
      schatten_two_unitary, schatten_two_unitary]; ring

/-- A bounded-diameter argument gives a dimension-uniform fallback for the small
unitary groups, under any probability law. -/
theorem unitary_logmean_small_dimension (n : ℕ) (hn : 1 ≤ n) (hn3 : n ≤ 3)
    [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsProbabilityMeasure μ]
    (F : Matrix.unitaryGroup (Fin n) ℂ → ℝ) (hF : AEMeasurable F μ)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ U V : Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ))) :
    Real.log (∫ U, Real.exp (F U) ∂μ) - 18 * L^2 / n ≤ ∫ U, F U ∂μ := by
  let R := 2 * L * Real.sqrt n
  have hbound : ∀ᵐ U ∂μ, F U ∈ Set.Icc (F 1 - R) (F 1 + R) := by
    filter_upwards [] with U
    have h := (hLip U 1).trans (mul_le_mul_of_nonneg_left (schatten_two_unitary_sub_le n U 1) hL)
    have habs : |F U - F 1| ≤ R := by dsimp only [R]; nlinarith
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    exact ⟨by linarith, by linarith⟩
  have h := logmean_le_mean_add_range_sq μ F hF (F 1 - R) (F 1 + R) hbound
  have hwidth : (F 1 + R - (F 1 - R))^2 / 8 = 2 * n * L^2 := by
    dsimp only [R]
    have hs := Real.sq_sqrt (Nat.cast_nonneg n)
    nlinarith
  rw [hwidth] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnsmall : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
  have hconst : 2 * (n : ℝ) * L^2 ≤ 18 * L^2 / n := by
    apply (le_div_iff₀ hn0).mpr
    have hn2 : (n : ℝ)^2 ≤ 9 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hn2 (sq_nonneg L)
    nlinarith
  linarith

end BosonicLearn.Prop5

end

/- Local helper source: Solutions.Prop2HaarConcentration -/
section
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn.Prop2
noncomputable section
set_option maxHeartbeats 800000

/-- Tensorized Haar tails imply a Gaussian exponential-moment bound with no
multiplicative prefactor. -/
theorem unitary_centered_mgf_large_dimension {n : ℕ} (hn : 4 ≤ n)
    (F : Matrix.unitaryGroup (Fin n) ℂ → ℝ) (hF : Continuous F)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V : Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ))) :
    (∫ U, Real.exp (F U - ∫ V, F V ∂unitaryHaar n) ∂unitaryHaar n) ≤
      Real.exp ((24 * L^2 / ((n : ℝ) - 2)) / 2) := by
  let G : Matrix.unitaryGroup (Fin n) ℂ → ℝ := fun U => F U - ∫ V, F V ∂unitaryHaar n
  let a : ℝ := 24 * L^2 / ((n : ℝ) - 2)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by positivity) (by linarith)
  have hG : Continuous G := hF.sub continuous_const
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
  have hRG : ∀ U, |G U| ≤ R := fun U => by
    simpa only [Real.norm_eq_abs] using hR U (Set.mem_univ _)
  apply le_exp_of_all_pow_le_three_mul _ (a / 2)
  intro K hK
  let μ := SpectrumLB.haarK n K
  let X : (Fin K → Matrix.unitaryGroup (Fin n) ℂ) → ℝ := fun U => ∑ i, G (U i)
  have hμ : μ = Measure.pi (fun _ : Fin K => unitaryHaar n) := haarK_eq_pi n K
  let : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hKa : 0 < (K : ℝ) * a := mul_pos hK0 ha
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hExp : Integrable (fun U => Real.exp ((X U)^2 / (2 * ((K : ℝ) * a)))) μ := by
    rw [hμ]
    exact integrable_exp_sq_sum_of_abs_le (unitaryHaar n) G hG.measurable R hRG K _ hKa
  have htail : ∀ u : ℝ, 0 < u →
      μ {U | u ≤ |X U|} ≤ ENNReal.ofReal (2 * Real.exp (-u^2 / ((K : ℝ) * a))) := by
    intro u hu
    have h := centered_sum_unitary_tail hn hK F hF L hL hLip u hu.le
    change μ.real {U | u ≤ |X U|} ≤ 2 * Real.exp (-u^2 / ((K : ℝ) * a)) at h
    calc
      _ = ENNReal.ofReal (μ.real {U | u ≤ |X U|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  have hweak := exp_moment_le_three_mul_of_abs_tail μ X hX ((K : ℝ) * a) hKa hExp htail 1
  simp only [one_mul, one_pow, mul_one] at hweak
  change (∫ U, Real.exp (∑ i : Fin K, G (U i)) ∂SpectrumLB.haarK n K) ≤ _ at hweak
  rw [integral_exp_sum_unitary] at hweak
  simpa only [mul_div_assoc] using hweak

/-- The large-dimensional logarithmic mean bound obtained from product Haar
concentration and tensor amplification. -/
theorem unitary_logmean_large_dimension {n : ℕ} (hn : 4 ≤ n)
    (F : Matrix.unitaryGroup (Fin n) ℂ → ℝ) (hF : Continuous F)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ U V : Matrix.unitaryGroup (Fin n) ℂ,
      |F U - F V| ≤ L * WHMultiplicativity.schattenNorm 2
        ((U : Matrix (Fin n) (Fin n) ℂ) - (V : Matrix (Fin n) (Fin n) ℂ))) :
    Real.log (∫ U, Real.exp (F U) ∂unitaryHaar n) - 24 * L^2 / n ≤
      ∫ U, F U ∂unitaryHaar n := by
  let m := ∫ U, F U ∂unitaryHaar n
  let a : ℝ := 24 * L^2 / ((n : ℝ) - 2)
  have h := unitary_centered_mgf_large_dimension hn F hF L hL hLip
  simp_rw [Real.exp_sub] at h
  rw [integral_div] at h
  have hM : 0 < ∫ U, Real.exp (F U) ∂unitaryHaar n :=
    integral_exp_pos (continuous_integrable_unitaryHaar _ (Real.continuous_exp.comp hF))
  have hlog : Real.log (∫ U, Real.exp (F U) ∂unitaryHaar n) ≤ m + a/2 := by
    apply (Real.log_le_iff_le_exp hM).mpr
    rw [Real.exp_add]
    exact (div_le_iff₀ (Real.exp_pos m)).mp h |>.trans_eq (mul_comm _ _)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hconst : a / 2 ≤ 24 * L^2 / n := by
    calc
      a / 2 = 12 * L^2 / ((n : ℝ) - 2) := by dsimp [a]; ring
      _ ≤ 24 * L^2 / n := by
        apply (div_le_div_iff₀ hn2 hn0).mpr
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) - 4 by linarith) (sq_nonneg L)]
  change Real.log (∫ U, Real.exp (F U) ∂unitaryHaar n) - 24 * L^2 / n ≤ m
  linarith

/-- A uniform logarithmic mean bound in every dimension. The only concentration
input is the pre-existing product-unitary tail theorem `SpectrumLB.eq_7_14`. -/
theorem haarUnitaryLogMeanBound24 : HaarUnitaryLogMeanBound 24 := by
  intro n hn F hF L hL hLip
  by_cases hL0 : L = 0
  · have hconst : F = fun _ => F 1 := by
      funext U
      have h := hLip U 1
      rw [hL0, zero_mul] at h
      exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
    rw [hconst]
    simp [hL0]
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    by_cases hn4 : 4 ≤ n
    · exact unitary_logmean_large_dimension hn4 F hF L hLpos hLip
    · have h := Prop5.unitary_logmean_small_dimension n hn (by omega) (unitaryHaar n)
        F hF.measurable.aemeasurable L hL hLip
      have hconst : 18 * L^2 / n ≤ 24 * L^2 / n := by gcongr; norm_num
      linarith

end
end BosonicLearn.Prop2

end

/- Local helper source: Solutions.Prop2Resolved -/
section
open MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal
namespace BosonicLearn

theorem proposition_2_reduced :
    ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ X₀ ∈ Ggood n, ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∀ (N : ℕ) (k : Fin N → ℕ) (ϕ : Fin N → Occupation (Fin n) → ℂ),
        (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
        ENNReal.ofReal (Real.exp (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))) ≤
          ∫⁻ Z, ENNReal.ofReal (∏ t,
              (∑' u, ∑' v, star (ϕ t u) *
                fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) u v * ϕ t v).re /
              (∑' u, ∑' v, star (ϕ t u) * fugacityCoeff (fugacityFamily ν ξ X₀) u v * ϕ t v).re)
            ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) :=
  proposition_2_of_haar_logmean 24 (by norm_num) Prop2.haarUnitaryLogMeanBound24

end BosonicLearn

end

open BosonicLearn MeasureTheory ProbabilityTheory
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ X₀ ∈ Ggood n, ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∀ (N : ℕ) (k : Fin N → ℕ) (ϕ : Fin N → Occupation (Fin n) → ℂ),
        (∀ t u, ∑ i, u i ≠ k t → ϕ t u = 0) → (∀ t, ϕ t ≠ 0) →
        ENNReal.ofReal (Real.exp (-(C * ξ ^ 2 * ∑ t, ((n : ℝ) * ν ^ 2 + (k t : ℝ) ^ 2 / n)))) ≤
          ∫⁻ Z, ENNReal.ofReal (∏ t,
              (∑' u, ∑' v, star (ϕ t u) *
                fugacityCoeff (fugacityFamily ν ξ (PhiMap X₀ ξ Z)) u v * ϕ t v).re /
              (∑' u, ∑' v, star (ϕ t u) * fugacityCoeff (fugacityFamily ν ξ X₀) u v * ϕ t v).re)
            ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)) := BosonicLearn.proposition_2_reduced
