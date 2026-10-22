-- Prove2me | solution 1 for CODATA.codata_self_consistent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:14:31.919877+00:00
-- url     : https://prove2.me/submissions/a864a06a-80b9-4b54-9fdf-e8f2215622fe

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

open CODATA

noncomputable def g71c_B {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (v w : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * G i j * w j

lemma g71c_B_symm {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : ∀ i j, G i j = G j i)
    (v w : Fin N → ℝ) : g71c_B G v w = g71c_B G w v := by
  unfold g71c_B; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  rw [hG]; ring

lemma g71c_B_sub_left {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (u v w : Fin N → ℝ) :
    g71c_B G (u - v) w = g71c_B G u w - g71c_B G v w := by
  unfold g71c_B; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; simp; ring

lemma g71c_B_sub_right {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (u v w : Fin N → ℝ) :
    g71c_B G u (v - w) = g71c_B G u v - g71c_B G u w := by
  unfold g71c_B; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; simp; ring

lemma g71c_B_mulVec {N M : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (A : Matrix (Fin N) (Fin M) ℝ)
    (d : Fin M → ℝ) (r : Fin N → ℝ) :
    g71c_B G (A.mulVec d) r = ∑ k, d k * ∑ i, ∑ j, A i k * G i j * r j := by
  unfold g71c_B
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

lemma g71c_resid_add {N M : ℕ} (L : LSQ N M) (x d : Fin M → ℝ) :
    resid L (x + d) = resid L x - L.A.mulVec d := by
  funext i; simp [resid, Matrix.mulVec_add]; ring

lemma g71c_chi {N M : ℕ} (L : LSQ N M) (x : Fin M → ℝ) :
    chiSq L x = g71c_B L.G (resid L x) (resid L x) := rfl

lemma g71c_expand {N M : ℕ} (L : LSQ N M) (hG : ∀ i j, L.G i j = L.G j i) (x d : Fin M → ℝ) :
    chiSq L (x + d) = chiSq L x - 2 * ∑ k, d k * ∑ i, ∑ j, L.A i k * L.G i j * resid L x j
      + g71c_B L.G (L.A.mulVec d) (L.A.mulVec d) := by
  rw [g71c_chi, g71c_chi, g71c_resid_add, g71c_B_sub_left, g71c_B_sub_right, g71c_B_sub_right,
    g71c_B_symm L.G hG (resid L x) (L.A.mulVec d), g71c_B_mulVec]
  ring

lemma g71c_min {N M : ℕ} (L : LSQ N M) (hG : IsSPD L.G) (x : Fin M → ℝ) (hn : SolvesNormal L x) :
    Minimizes L x := by
  have hpos : ∀ v, 0 ≤ g71c_B L.G v v := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp [g71c_B]
    · exact (hG.2 v hv).le
  intro z
  have h1 := g71c_expand L hG.1 x (z - x)
  rw [add_sub_cancel] at h1
  rw [h1]
  have : ∑ k, (z - x) k * ∑ i, ∑ j, L.A i k * L.G i j * resid L x j = 0 := by
    apply Finset.sum_eq_zero; intro k _; rw [hn k, mul_zero]
  rw [this]; linarith [hpos (L.A.mulVec (z - x))]

lemma g71c_corr {N : ℕ} (V : Matrix (Fin N) (Fin N) ℝ) (hV : ∀ k, 0 < V k k) (i j : Fin N) :
    corr (expandD (fun _ => 39/10) V) i j = corr V i j := by
  simp only [corr, expandD, Matrix.of_apply]
  have hi := hV i; have hj := hV j
  have : (39/10:ℝ) * (39/10) * V i i * ((39/10) * (39/10) * V j j)
      = ((39/10) * (39/10))^2 * (V i i * V j j) := by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have : 0 < Real.sqrt (V i i * V j j) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-!
# The 2022 adjustment is self-consistent

The goal theorem of the mission packages the milestones into the
statement that the two adjustments of the 2022 CODATA report are
self-consistent. Let L be the main adjustment: 133 input data for 79
adjusted constants, hence 54 degrees of freedom. Let LG be the
separate adjustment of the sixteen values of the Newtonian constant of
gravitation: 16 input data for a single adjusted constant, hence 15
degrees of freedom. Suppose both weight matrices are symmetric and
strictly positive definite, the uncertainties of the sixteen values of
G are positive and their self-correlations are one, and x and xg
solve the respective normal equations. Then the degrees of freedom are
54 and 15; x and xg minimize their chi-square statistics; the Birge
ratios sqrt(44.2/54) and sqrt(12.9/15) round to the printed values
0.90 and 0.93; the expansion of the covariance matrix of the sixteen
values of G by the expansion factor 3.9 preserves every correlation
coefficient; a single rational relative-uncertainty witness
reproduces the printed two-significant-digit uncertainties of the
alpha family; and the exact derived constants K_J, R_K, Phi_0, G_0,
G_0⁻¹, F, R, the electronvolt and h in eV Hz⁻¹ agree with the printed
digit strings of Table XXXIII.

The mission source is P. J. Mohr, D. B. Newell, B. N. Taylor and
E. Tiesinga, CODATA recommended values of the fundamental physical
constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi
10.1063/5.0279860, and the identical Rev. Mod. Phys. 97, 025002
(2025), doi 10.1103/RevModPhys.97.025002, section XII and Tables
XXXII-XXXIII.
-/

open CODATA
/-- The two adjustments of the 2022 CODATA report are self-consistent:
the main adjustment of 133 input data for 79 adjusted constants and
the separate adjustment of the sixteen values of the Newtonian
constant of gravitation have 54 and 15 degrees of freedom; solutions
of the normal equations minimize the chi-square statistic; the
resulting Birge ratios round to the printed 0.90 and 0.93; the
expansion factor 3.9 applied to the covariance matrix of the sixteen
values of G preserves every correlation; one rational
relative-uncertainty witness reproduces the printed uncertainties of
the alpha family; and the exact derived constants agree with their
printed digit strings. -/
theorem solution (L : LSQ 133 79) (LG : LSQ 16 1)
    (hG : IsSPD L.G) (hGg : IsSPD LG.G) (hu : ∀ i, 0 < LG.u i)
    (hur : ∀ i, LG.r i i = 1) (x : Fin 79 → ℝ) (hx : SolvesNormal L x)
    (xg : Fin 1 → ℝ) (hxg : SolvesNormal LG xg) :
    dof 133 79 = 54 ∧ dof 16 1 = 15 ∧
      Minimizes L x ∧ Minimizes LG xg ∧
      895/1000 ≤ Real.sqrt (442/10/54) ∧
        Real.sqrt (442/10/54) < 905/1000 ∧
      925/1000 ≤ Real.sqrt (129/10/15) ∧
        Real.sqrt (129/10/15) < 935/1000 ∧
      ∀ i j, corr (expandD (fun _ => 39/10) (covMat LG)) i j
        = corr (covMat LG) i j ∧
      (∃ ur : ℚ,
        155/(10:ℚ)^12 ≤ ur ∧ ur < 165/(10:ℚ)^12 ∧
        105/(10:ℚ)^14 ≤ ur * alphaVal ∧ ur * alphaVal < 115/(10:ℚ)^14 ∧
        205/(10:ℚ)^10 ≤ ur * alphaInvVal ∧
          ur * alphaInvVal < 215/(10:ℚ)^10 ∧
        195/(10:ℚ)^18 ≤ ur * mu0Val ∧ ur * mu0Val < 205/(10:ℚ)^18 ∧
        135/(10:ℚ)^23 ≤ ur * eps0Val ∧
          ur * eps0Val < 145/(10:ℚ)^23 ∧
        585/(10:ℚ)^10 ≤ ur * z0Val ∧ ur * z0Val < 595/(10:ℚ)^10) ∧
      4835978484/(10:ℚ)^4 ≤ kjVal/(10:ℚ)^9 ∧
        kjVal/(10:ℚ)^9 < 4835978485/(10:ℚ)^4 ∧
      2581280745/(10:ℚ)^5 ≤ rkVal ∧ rkVal < 2581280746/(10:ℚ)^5 ∧
      2067833848/(10:ℚ)^24 ≤ phi0Val ∧
        phi0Val < 2067833849/(10:ℚ)^24 ∧
      7748091729/(10:ℚ)^14 ≤ g0Val ∧
        g0Val < 7748091730/(10:ℚ)^14 ∧
      1290640372/(10:ℚ)^5 ≤ g0invVal ∧
        g0invVal < 1290640373/(10:ℚ)^5 ∧
      9648533212/(10:ℚ)^5 ≤ faradayVal ∧
        faradayVal < 9648533213/(10:ℚ)^5 ∧
      8314462618/(10:ℚ)^9 ≤ gasVal ∧ gasVal < 8314462619/(10:ℚ)^9 ∧
      eVoltVal = 1602176634/(10:ℚ)^28 ∧
      4135667696/(10:ℚ)^24 ≤ h_eV ∧
        h_eV < 4135667697/(10:ℚ)^24 := by
  have hdiag : ∀ i, 0 < covMat LG i i := by
    intro i; simp only [covMat, Matrix.of_apply, hur i, one_mul]; have := hu i; positivity
  refine ⟨rfl, rfl, g71c_min L hG x hx, g71c_min LG hGg xg hxg, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  intro i j
  refine ⟨g71c_corr _ hdiag i j, ⟨156/(10:ℚ)^12, ?_⟩, ?_⟩
  · simp only [alphaVal, alphaInvVal, mu0Val, eps0Val, z0Val]
    norm_num
  · simp only [kjVal, rkVal, phi0Val, g0Val, g0invVal, faradayVal, gasVal, eVoltVal, h_eV, hVal, eVal, kVal, naVal]
    norm_num


