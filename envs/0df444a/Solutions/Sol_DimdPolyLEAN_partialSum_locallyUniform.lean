-- Prove2me | solution 1 for DimdPolyLEAN.partialSum_locallyUniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:31.721121+00:00
-- url     : https://prove2.me/submissions/d2c8ef0b-e450-4e88-a934-9cc004244d1d

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_box_subset_box
public import Theorems.Thm_DimdPolyLEAN_finite_subset_box
public import Theorems.Thm_DimdPolyLEAN_partialSum_tendsto_toFun_pointwise
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_phi_explicit
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private lemma factorial_ratio_le_pow_succ
    {n k j : ℕ} (hjn : j ≤ n) (hjk : j ≤ k) :
    (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) ≤ (n + 1 : ℝ) ^ k := by
  have hnat : n.descFactorial j ≤ (n + 1) ^ k := by
    calc
      n.descFactorial j ≤ n ^ j := Nat.descFactorial_le_pow _ _
      _ ≤ (n + 1) ^ j := Nat.pow_le_pow_left n.le_succ _
      _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos _) hjk
  have hdiv_nat : n.descFactorial j = n.factorial / (n - j).factorial := by
    rw [Nat.descFactorial_eq_div hjn]
  have hdiv :
      (Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ) = n.descFactorial j := by
    rw [hdiv_nat, Nat.cast_div (Nat.factorial_dvd_factorial (Nat.sub_le n j))]
    positivity
  rw [hdiv]
  exact_mod_cast hnat
private lemma choose_partial_sum_le_pow_two (k n : ℕ) :
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ)) ≤
      (2 : ℝ) ^ k := by
  calc
    Finset.sum (Finset.range (min k n + 1)) (fun j => (Nat.choose k j : ℝ))
        ≤ Finset.sum (Finset.range (k + 1)) (fun j => (Nat.choose k j : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · simp_all
          · simp_all
    _ = (2 : ℝ) ^ k := by exact_mod_cast Nat.sum_range_choose k
private lemma summable_nat_pow_mul_pow_div_factorial_nonneg
    (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)) := by
  let f : ℕ → ℝ := fun n => ((n + 1 : ℝ) ^ m) * x ^ n / (Nat.factorial n : ℝ)
  rw [← @summable_nat_add_iff ℝ _ _ _ _ m]
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ =>
      ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ))) ?_ ?_ ?_
  · intro n
    positivity
  · intro n
    have hdesc_nat : (n + 1) ^ m ≤ (n + m).descFactorial m := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.pow_sub_le_descFactorial (n + m) m)
    have hpow_real :
        ((n + m + 1 : ℝ) ^ m) ≤
          (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by
      have hdesc :
          ((n + 1 : ℝ) ^ m) ≤ (((n + m).descFactorial m : ℕ) : ℝ) := by exact_mod_cast hdesc_nat
      calc
        ((n + m + 1 : ℝ) ^ m) ≤ (((m + 1 : ℝ) * (n + 1)) ^ m) := by
          gcongr
          nlinarith only []
        _ = (m + 1 : ℝ) ^ m * (n + 1 : ℝ) ^ m := by rw [mul_pow]
        _ ≤ (m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ) := by gcongr
    have hfact :
        (Nat.factorial n : ℝ) * (((n + m).descFactorial m : ℕ) : ℝ) =
          (Nat.factorial (n + m) : ℝ) := by
      have hfact_nat : n.factorial * (n + m).descFactorial m = (n + m).factorial := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.factorial_mul_descFactorial (show m ≤ n + m by omega))
      exact_mod_cast hfact_nat
    have hcalc :
        (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) * x ^ (n + m)) /
            (Nat.factorial (n + m) : ℝ) =
          ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := by
      rw [pow_add, ← hfact]
      have hnfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      have hndesc_nat : (n + m).descFactorial m ≠ 0 :=
        Nat.ne_of_gt (Nat.descFactorial_pos.mpr (show m ≤ n + m by omega))
      have hndesc : (((n + m).descFactorial m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hndesc_nat
      field_simp [hnfact, hndesc]
    calc
      f (n + m) =
          ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) /
            (Nat.factorial (n + m) : ℝ) := by simp [f]
      _ ≤ (((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) *
              x ^ (n + m)) / (Nat.factorial (n + m) : ℝ) := by
            have hpowx :
                ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                  ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                    x ^ (n + m) := mul_le_mul_of_nonneg_right hpow_real (pow_nonneg hx _)
            have hfacpos : 0 < (Nat.factorial (n + m) : ℝ) := by positivity
            rw [div_le_iff₀ hfacpos]
            calc
              ((n + m + 1 : ℝ) ^ m) * x ^ (n + m) ≤
                  ((m + 1 : ℝ) ^ m * (((n + m).descFactorial m : ℕ) : ℝ)) *
                    x ^ (n + m) := hpowx
              _ =
                  ((((m + 1 : ℝ) ^ m) * (((n + m).descFactorial m : ℕ) : ℝ) *
                      x ^ (n + m)) / (Nat.factorial (n + m) : ℝ)) *
                    (Nat.factorial (n + m) : ℝ) := by
                    have hfacne : (Nat.factorial (n + m) : ℝ) ≠ 0 := by positivity
                    field_simp [hfacne]
      _ = ((m + 1 : ℝ) ^ m * x ^ m) * (x ^ n / (Nat.factorial n : ℝ)) := hcalc
  · simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
      (Real.summable_pow_div_factorial x).mul_left ((m + 1 : ℝ) ^ m * x ^ m)
private lemma phiMajorant_nonneg
    {k n : Nat} {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ phiMajorant k n R := by
  unfold phiMajorant
  positivity
private lemma summable_phiMajorant_sq
    (k : Nat) {R : ℝ} (hR : 1 ≤ R) :
    Summable (fun n : Nat => phiMajorant k n R ^ 2) := by
  let C : ℝ := (((2 : ℝ) ^ k) ^ 2 * (R ^ k) ^ 2) / (Nat.factorial k : ℝ)
  have hbase0 :
      Summable
        (fun n : ℕ =>
          ((n + 1 : ℝ) ^ (2 * k)) * (R ^ 2) ^ n / (Nat.factorial n : ℝ)) := by
    apply summable_nat_pow_mul_pow_div_factorial_nonneg
    positivity
  have hbase :
      Summable
        (fun n : ℕ => (((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) /
          (Nat.factorial n : ℝ)) := by
    refine hbase0.congr ?_
    intro n
    rw [← pow_mul, ← pow_mul]
    simp [pow_mul, Nat.mul_comm]
  have hmajorant :
      Summable
        (fun n : ℕ =>
          C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ))) := hbase.mul_left C
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg (phiMajorant k n R)) ?_ hmajorant
  intro n
  have hsqrt_ne :
      Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by positivity
  have : phiMajorant k n R ^ 2 =
      C * ((((n + 1 : ℝ) ^ k) ^ 2 * (R ^ n) ^ 2) / (Nat.factorial n : ℝ)) := by
    dsimp [phiMajorant, C]
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt (by positivity)]
  exact this.le
private lemma phi1D_norm_le_majorant
    {k n : ℕ} {R : ℝ} (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖phi1D k n z‖ ≤ phiMajorant k n R := by
  let S := Finset.range (min k n + 1)
  let term : ℕ → ℂ := fun j =>
    (-1 : ℂ) ^ j * ↑(k.choose j) * (↑n.factorial / ↑(n - j).factorial) *
      z ^ (n - j) * star z ^ (k - j)
  let common : ℝ := ((n + 1 : ℝ) ^ k) * R ^ k * R ^ n
  have hphi : phi1D k n z = HermitekLEAN.Phi k n z := by
    simpa [Hermite1DimdLEAN.oneDimPhi, HermitekLEAN.Phi] using phi1D_eq_oneDimPhi k n z
  rw [hphi, HermitekLEAN.phi_explicit]
  have hsum_norm : ‖Finset.sum S term‖ ≤ Finset.sum S (fun j => ‖term j‖) :=
    norm_sum_le _ _
  have hterm_bound : ∀ j ∈ S, ‖term j‖ ≤ (Nat.choose k j : ℝ) * common := by
    intro j hj
    have hjk : j ≤ k := by
      simp [S] at hj
      omega
    have hjn : j ≤ n := by
      simp [S] at hj
      omega
    have hratio := factorial_ratio_le_pow_succ hjn hjk
    have hz1 : ‖z‖ ^ (n - j) ≤ R ^ n :=
      le_trans (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_le_pow_right₀ hR (Nat.sub_le _ _))
    have hz2 : ‖z‖ ^ (k - j) ≤ R ^ k :=
      le_trans (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_le_pow_right₀ hR (Nat.sub_le _ _))
    calc
      ‖term j‖ =
          (Nat.choose k j : ℝ) *
            ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
              ‖z‖ ^ (n - j) * ‖z‖ ^ (k - j) := by
            dsimp [term]
            simp [norm_pow]
      _ ≤ (Nat.choose k j : ℝ) * ((n + 1 : ℝ) ^ k) * R ^ n * R ^ k := by gcongr
      _ = (Nat.choose k j : ℝ) * common := by
            dsimp [common]
            ring
  have hsum_bound :
      Finset.sum S (fun j => ‖term j‖) ≤
        Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) :=
    Finset.sum_le_sum (fun j hj => hterm_bound j hj)
  have hsum_factor :
      Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) =
        (Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common := by rw [Finset.sum_mul]
  have hfront_nonneg :
      0 ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ :=
    norm_nonneg _
  have hfront :
      ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ =
        ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) := by
    rw [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), one_div]
  calc
    ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
        Finset.sum S term‖
        ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
            Finset.sum S (fun j => ‖term j‖) := le_trans (norm_mul_le _ _) <|
            mul_le_mul_of_nonneg_left hsum_norm (norm_nonneg _)
    _ ≤ ‖((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ)‖ *
            Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) :=
          mul_le_mul_of_nonneg_left hsum_bound hfront_nonneg
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
            Finset.sum S (fun j => (Nat.choose k j : ℝ) * common) := by rw [hfront]
    _ = ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
            ((Finset.sum S (fun j => (Nat.choose k j : ℝ))) * common) := by rw [hsum_factor]
    _ ≤ ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℝ) *
            (((2 : ℝ) ^ k) * common) := by
          gcongr
          exact choose_partial_sum_le_pow_two k n
    _ = phiMajorant k n R := by
          dsimp [phiMajorant, common]
          rw [div_eq_mul_inv]
          ring
private lemma phiMajorant_multi_sq_summable
    {d : Nat} (kappa : MultiIndex d) {R : ℝ} (hR : 1 ≤ R) :
    Summable
      (fun alpha : Idx d =>
        (Finset.prod Finset.univ fun q : Fin d => phiMajorant (kappa q) (alpha q) R) ^ 2) := by
  classical
  refine summable_of_sum_le
    (c := Finset.prod Finset.univ
      (fun q : Fin d => ∑' n : Nat, phiMajorant (kappa q) n R ^ 2))
    (fun alpha : Idx d => sq_nonneg _) ?_
  intro E
  let J : Fin d -> Nat := fun q => Finset.sup E (fun alpha : Idx d => alpha q)
  let B : Finset (Idx d) := Fintype.piFinset fun q : Fin d => Finset.range (J q + 1)
  have hE_subset : E ⊆ B := by
    intro alpha halpha
    dsimp [B]
    rw [Fintype.mem_piFinset]
    intro q
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (s := E) (f := fun beta : Idx d => beta q) halpha
  have hsum_E_le_B :
      Finset.sum E
          (fun alpha : Idx d =>
            (Finset.prod Finset.univ fun q : Fin d =>
              phiMajorant (kappa q) (alpha q) R) ^ 2) ≤
        Finset.sum B
          (fun alpha : Idx d =>
            (Finset.prod Finset.univ fun q : Fin d =>
              phiMajorant (kappa q) (alpha q) R) ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hE_subset
      (by intro alpha _ _; exact sq_nonneg _)
  have hbox_eq :
      Finset.sum B
          (fun alpha : Idx d =>
            (Finset.prod Finset.univ fun q : Fin d =>
              phiMajorant (kappa q) (alpha q) R) ^ 2) =
        Finset.prod Finset.univ
          (fun q : Fin d =>
            Finset.sum (Finset.range (J q + 1))
              (fun n : Nat => phiMajorant (kappa q) n R ^ 2)) := by
    dsimp [B]
    symm
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    simp [Finset.prod_pow]
  have hprod_le :
      Finset.prod Finset.univ
          (fun q : Fin d =>
            Finset.sum (Finset.range (J q + 1))
              (fun n : Nat => phiMajorant (kappa q) n R ^ 2)) ≤
        Finset.prod Finset.univ
          (fun q : Fin d => ∑' n : Nat, phiMajorant (kappa q) n R ^ 2) :=
    Finset.prod_le_prod
      (fun q _ => Finset.sum_nonneg fun n _ => sq_nonneg _)
      (fun q _ => (summable_phiMajorant_sq (kappa q) hR).sum_le_tsum
          (Finset.range (J q + 1)) (fun n _ => sq_nonneg _))
  exact le_trans hsum_E_le_B (by rw [hbox_eq]; exact hprod_le)
private theorem uniformCauchySeqOn_of_summable_bound
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) {K : Set (Cd d)}
    {M : Idx d -> ℝ} (hM : Summable M)
    (hbound : ∀ alpha : Idx d, ∀ z ∈ K,
      ‖coeffSkappa U alpha * Phi kappa alpha z‖ ≤ M alpha) :
    UniformCauchySeqOn (fun J : MultiIndex d => partialSum kappa U J) Filter.atTop K := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rcases (summable_iff_vanishing_norm.mp hM) (ε / 2) hε2 with ⟨E0, hE0⟩
  rcases finite_subset_box E0 with ⟨J0, hE0J0⟩
  refine ⟨J0, ?_⟩
  intro J hJ L hL z hzK
  let term : Idx d -> ℂ := fun alpha => coeffSkappa U alpha * Phi kappa alpha z
  have tail_bound (N : MultiIndex d) (hN : J0 ≤ N) :
      dist (partialSum kappa U N z) (partialSum kappa U J0 z) < ε / 2 := by
    have hsubset : box J0 ⊆ box N := box_subset_box hN
    have htail_eq :
        partialSum kappa U N z - partialSum kappa U J0 z =
          ∑ alpha ∈ box N \ box J0, term alpha := by
      unfold partialSum
      have hsum :=
        Finset.sum_sdiff (s₁ := box J0) (s₂ := box N) (f := term) hsubset
      dsimp [term] at hsum ⊢
      simp_all
    have hdisj : Disjoint (box N \ box J0) E0 := by
      rw [Finset.disjoint_left]
      intro alpha halpha hαE0
      exact (Finset.mem_sdiff.mp halpha).2 (hE0J0 hαE0)
    have htail_lt : ‖∑ alpha ∈ box N \ box J0, M alpha‖ < ε / 2 := hE0 _ hdisj
    rw [dist_eq_norm, htail_eq]
    calc
      ‖∑ alpha ∈ box N \ box J0, term alpha‖
          ≤ ∑ alpha ∈ box N \ box J0, ‖term alpha‖ := norm_sum_le _ _
      _ ≤ ∑ alpha ∈ box N \ box J0, M alpha := by
            refine Finset.sum_le_sum ?_
            intro alpha halpha
            exact hbound alpha z hzK
      _ = ‖∑ alpha ∈ box N \ box J0, M alpha‖ := by
            rw [Real.norm_eq_abs]
            exact (abs_of_nonneg (Finset.sum_nonneg fun alpha halpha =>
              le_trans (norm_nonneg _) (hbound alpha z hzK))).symm
      _ < ε / 2 := htail_lt
  have hJtail := tail_bound J hJ
  have hLtail := tail_bound L hL
  calc
    dist (partialSum kappa U J z) (partialSum kappa U L z)
        ≤ dist (partialSum kappa U J z) (partialSum kappa U J0 z) +
            dist (partialSum kappa U J0 z) (partialSum kappa U L z) :=
          dist_triangle _ _ _
    _ = dist (partialSum kappa U J z) (partialSum kappa U J0 z) +
          dist (partialSum kappa U L z) (partialSum kappa U J0 z) := by
          rw [dist_comm (partialSum kappa U J0 z) (partialSum kappa U L z)]
    _ < ε := by linarith only [hJtail, hLtail]
private lemma compact_exists_coord_bound
    {d : Nat} {K : Set (Cd d)} (hK : IsCompact K) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ z ∈ K, ∀ q : Fin d, ‖z q‖ ≤ R := by
  rcases hK.isBounded.subset_closedBall (0 : Cd d) with ⟨r, hr⟩
  refine ⟨max 1 r, le_max_left _ _, ?_⟩
  intro z hz q
  have hzball := hr hz
  have hznorm : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
  exact le_trans (norm_le_pi_norm z q) (le_trans hznorm (le_max_right _ _))
private lemma partialSum_uniformCauchy_on_compact
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) {K : Set (Cd d)}
    (hK : IsCompact K) :
    UniformCauchySeqOn (fun J : MultiIndex d => partialSum kappa U J) Filter.atTop K := by
  classical
  rcases compact_exists_coord_bound hK with ⟨R, hR, hcoord⟩
  let Bprod : Idx d -> ℝ := fun alpha =>
    Finset.prod Finset.univ fun q : Fin d => phiMajorant (kappa q) (alpha q) R
  let M : Idx d -> ℝ := fun alpha => ‖coeffSkappa U alpha‖ * Bprod alpha
  have hR_nonneg : 0 ≤ R := le_trans zero_le_one hR
  have hBprod_nonneg : ∀ alpha : Idx d, 0 ≤ Bprod alpha := by
    intro alpha
    dsimp [Bprod]
    exact Finset.prod_nonneg fun q _ => phiMajorant_nonneg hR_nonneg
  have hM_summable : Summable M := by
    have hcoeff : Summable (fun alpha : Idx d => ‖coeffSkappa U alpha‖ ^ 2) := by
      exact U.summable_norm_sq
    have hBsq : Summable (fun alpha : Idx d => Bprod alpha ^ 2) := by
      exact phiMajorant_multi_sq_summable kappa hR
    refine Summable.of_nonneg_of_le (fun alpha => ?_) ?_ ((hcoeff.add hBsq).div_const 2)
    · exact mul_nonneg (norm_nonneg _) (hBprod_nonneg alpha)
    · intro alpha
      dsimp [M]
      nlinarith only [sq_nonneg (‖coeffSkappa U alpha‖ - Bprod alpha)]
  refine uniformCauchySeqOn_of_summable_bound kappa U hM_summable ?_
  intro alpha z hzK
  have hPhi : ‖Phi kappa alpha z‖ ≤ Bprod alpha := by
    rw [show ‖Phi kappa alpha z‖ =
        Finset.prod Finset.univ
          (fun q : Fin d => ‖phi1D (kappa q) (alpha q) (z q)‖) by
      simp [Phi, norm_prod]]
    exact Finset.prod_le_prod
      (by intro q _; exact norm_nonneg _)
      (by intro q _; exact phi1D_norm_le_majorant hR (hcoord z hzK q))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hPhi (norm_nonneg _)
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    BoxPartialSumsLocallyUniformCauchy kappa U := by
  let _ := hd
  have hCauchy : ∀ K : Set (Cd d), IsCompact K ->
      UniformCauchySeqOn (fun J : MultiIndex d => partialSum kappa U J) Filter.atTop K := by
    intro K hK
    exact partialSum_uniformCauchy_on_compact kappa U hK
  refine ⟨hCauchy, ?_⟩
  change TendstoLocallyUniformly
    (fun J : MultiIndex d => partialSum kappa U J) (toFun kappa U) Filter.atTop
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  exact (hCauchy K hK).tendstoUniformlyOn_of_tendsto fun z _ =>
    partialSum_tendsto_toFun_pointwise kappa U z
end DimdPolyLEAN
