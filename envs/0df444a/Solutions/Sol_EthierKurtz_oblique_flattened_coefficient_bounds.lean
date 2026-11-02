-- Prove2me | solution 1 for EthierKurtz.oblique_flattened_coefficient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T23:22:48.011364+00:00
-- url     : https://prove2.me/submissions/d005234f-10d4-4f0e-9ffc-4440fff3454e

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology

namespace ObliqueLib
/-- Euclidean space of dimension `d`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Normalized Gaussian of "variance parameter" `s`: `G s z = (π s)^(-d/2) exp(-|z|^2/s)`. -/
noncomputable def G (d : ℕ) (s : ℝ) (z : Eu d) : ℝ :=
  (π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s)

section Comp2

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Uniform `C^{2,μ}`-type bounds of `(f, Df, D2f)` on a set `T` with one constant `K`. -/
structure C2B (T : Set E) (μ K : ℝ) (f : E → F) (Df : E → E →L[ℝ] F)
    (D2f : E → E →L[ℝ] E →L[ℝ] F) : Prop where
  hK : 0 ≤ K
  lip : ∀ x ∈ T, ∀ y ∈ T, ‖f x - f y‖ ≤ K * ‖x - y‖
  b1 : ∀ x ∈ T, ‖Df x‖ ≤ K
  lip1 : ∀ x ∈ T, ∀ y ∈ T, ‖Df x - Df y‖ ≤ K * ‖x - y‖
  b2 : ∀ x ∈ T, ‖D2f x‖ ≤ K
  hol2 : ∀ x ∈ T, ∀ y ∈ T, ‖D2f x - D2f y‖ ≤ K * ‖x - y‖ ^ μ

end Comp2

section Glue

variable {n : ℕ}

lemma coord_le (v : Eu n) (i : Fin n) : |v i| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm v (EuclideanSpace.single i (1 : ℝ))
  rw [EuclideanSpace.inner_single_right, EuclideanSpace.norm_single, norm_one, mul_one] at h
  simpa using h

end Glue

section IFT

variable {d : ℕ}

end IFT

section OpTrans

variable {d : ℕ}

end OpTrans

section CutHelp

variable {d : ℕ}

end CutHelp

section ObChartS

end ObChartS

section VarDef

end VarDef

section Pull

variable {d : ℕ}

lemma two_rpow_le {μ t : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (ht : 0 ≤ t) : (2 * t) ^ μ ≤ 2 * t ^ μ := by
  rw [Real.mul_rpow (by norm_num) ht]
  gcongr
  calc (2 : ℝ) ^ μ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
    _ = 2 := Real.rpow_one 2

end Pull

section NormA

variable {d : ℕ}

end NormA

section VarA

variable {d : ℕ}

end VarA

section PullA

variable {d : ℕ}

/-- second-order coefficient of the pulled-back operator relative to `½ A0`. -/
noncomputable def alTA (L : Eu d →L[ℝ] Eu d) (a : Matrix (Fin d) (Fin d) ℝ) (A0 : Matrix (Fin d) (Fin d) ℝ)
    (k l : Fin d) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, a i j * L (EuclideanSpace.single i (1 : ℝ)) k * L (EuclideanSpace.single j (1 : ℝ)) l
    - A0 k l)

/-- first-order coefficient of the pulled-back operator. -/
noncomputable def betTA (D2 : Eu d →L[ℝ] Eu d →L[ℝ] Eu d) (L : Eu d →L[ℝ] Eu d) (a : Matrix (Fin d) (Fin d) ℝ)
    (bb : Eu d) (k : Fin d) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, a i j * D2 (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k)
    + L bb k

end PullA

section CoefA

variable {d : ℕ}

lemma coA_le (A : Eu d →L[ℝ] Eu d) (i j : Fin d) : |A (EuclideanSpace.single i (1 : ℝ)) j| ≤ ‖A‖ := by
  refine (coord_le _ _).trans ?_
  have := A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
  simpa using this

lemma coB_le (B : Eu d →L[ℝ] Eu d →L[ℝ] Eu d) (i j k : Fin d) :
    |B (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k| ≤ ‖B‖ := by
  refine (coord_le _ _).trans ?_
  have := B.le_opNorm₂ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
  simpa using this

lemma alTA_id (A0 : Matrix (Fin d) (Fin d) ℝ) (k l : Fin d) :
    alTA (ContinuousLinearMap.id ℝ (Eu d)) A0 A0 k l = 0 := by
  unfold alTA
  simp only [ContinuousLinearMap.id_apply, EuclideanSpace.single_apply]
  simp [mul_ite, Finset.sum_ite_eq]

lemma abs_alTA_sub_le (L L' : Eu d →L[ℝ] Eu d) (a a' A0 : Matrix (Fin d) (Fin d) ℝ) (k l : Fin d) :
    |alTA L a A0 k l - alTA L' a' A0 k l| ≤
      (1 / 2 : ℝ) * ((∑ i, ∑ j, |a i j - a' i j|) * ‖L‖ ^ 2 +
        (∑ i, ∑ j, |a' i j|) * ((‖L‖ + ‖L'‖) * ‖L - L'‖)) := by
  have hs : alTA L a A0 k l - alTA L' a' A0 k l = (1 / 2 : ℝ) * ∑ i, ∑ j,
      ((a i j - a' i j) * (L (EuclideanSpace.single i 1) k * L (EuclideanSpace.single j 1) l) +
        a' i j * (L (EuclideanSpace.single i 1) k * L (EuclideanSpace.single j 1) l -
          L' (EuclideanSpace.single i 1) k * L' (EuclideanSpace.single j 1) l)) := by
    unfold alTA
    rw [← mul_sub]; congr 1
    rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hd : ∀ m n : Fin d, |L (EuclideanSpace.single m 1) n - L' (EuclideanSpace.single m 1) n| ≤ ‖L - L'‖ :=
    fun m n => by
      have := coA_le (L - L') m n
      simpa using this
  have hterm : ∀ i j, |(a i j - a' i j) * (L (EuclideanSpace.single i 1) k * L (EuclideanSpace.single j 1) l) +
        a' i j * (L (EuclideanSpace.single i 1) k * L (EuclideanSpace.single j 1) l -
          L' (EuclideanSpace.single i 1) k * L' (EuclideanSpace.single j 1) l)| ≤
      |a i j - a' i j| * ‖L‖ ^ 2 + |a' i j| * ((‖L‖ + ‖L'‖) * ‖L - L'‖) := by
    intro i j
    have h1 := coA_le L i k
    have h2 := coA_le L j l
    have h3 := coA_le L' i k
    have e1 : L (EuclideanSpace.single i 1) k * L (EuclideanSpace.single j 1) l -
          L' (EuclideanSpace.single i 1) k * L' (EuclideanSpace.single j 1) l =
        (L (EuclideanSpace.single i 1) k - L' (EuclideanSpace.single i 1) k) * L (EuclideanSpace.single j 1) l +
          L' (EuclideanSpace.single i 1) k * (L (EuclideanSpace.single j 1) l - L' (EuclideanSpace.single j 1) l) := by
      ring
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, sq]
      gcongr
    · rw [abs_mul, e1]
      gcongr
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |L (EuclideanSpace.single i 1) k - L' (EuclideanSpace.single i 1) k| * |L (EuclideanSpace.single j 1) l| +
            |L' (EuclideanSpace.single i 1) k| * |L (EuclideanSpace.single j 1) l - L' (EuclideanSpace.single j 1) l|
          ≤ ‖L - L'‖ * ‖L‖ + ‖L'‖ * ‖L - L'‖ := by
            gcongr
            · exact hd i k
            · exact hd j l
        _ = (‖L‖ + ‖L'‖) * ‖L - L'‖ := by ring
  rw [hs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j).trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, Finset.sum_mul]

lemma abs_betTA_sub_le (D2 D2' : Eu d →L[ℝ] Eu d →L[ℝ] Eu d) (L L' : Eu d →L[ℝ] Eu d)
    (a a' : Matrix (Fin d) (Fin d) ℝ) (bb bb' : Eu d) (k : Fin d) :
    |betTA D2 L a bb k - betTA D2' L' a' bb' k| ≤
      (1 / 2 : ℝ) * ((∑ i, ∑ j, |a i j - a' i j|) * ‖D2‖ + (∑ i, ∑ j, |a' i j|) * ‖D2 - D2'‖) +
        (‖L - L'‖ * ‖bb‖ + ‖L'‖ * ‖bb - bb'‖) := by
  have hs : betTA D2 L a bb k - betTA D2' L' a' bb' k = (1 / 2 : ℝ) * ∑ i, ∑ j,
      ((a i j - a' i j) * D2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) k +
        a' i j * (D2 - D2') (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) k) +
      ((L - L') bb k + L' (bb - bb') k) := by
    unfold betTA
    simp only [ContinuousLinearMap.sub_apply, PiLp.sub_apply, map_sub]
    have : ∀ i j, (a i j - a' i j) * D2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) k +
        a' i j * (D2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) k -
          D2' (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) k) =
        a i j * D2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) k -
          a' i j * D2' (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) k := fun i j => by ring
    simp only [this, Finset.sum_sub_distrib]
    ring
  rw [hs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) (le_of_eq (abs_mul _ _)))).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      add_le_add (mul_le_mul_of_nonneg_left (coB_le D2 i j k) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (coB_le (D2 - D2') i j k) (abs_nonneg _))).trans (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, Finset.sum_mul]
  · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (coord_le _ _).trans ((L - L').le_opNorm bb)
    · refine (coord_le _ _).trans (L'.le_opNorm _)

/-- coefficient bounds in z-space for the general operator, frozen at `A0 = a x0`. -/
theorem coef_boundsA {S Z : Set (Eu d)} {μ K ρ Ka : ℝ} {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d}
    {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d} (hC : C2B S μ K Θ DΘ D2Θ) {x0 : Eu d} (hx0 : x0 ∈ S)
    (hD0 : DΘ x0 = ContinuousLinearMap.id ℝ (Eu d)) {Λ : Eu d → Eu d} (hΛS : ∀ z ∈ Z, Λ z ∈ S)
    (h0Z : (0 : Eu d) ∈ Z) (hΛ0 : Λ 0 = x0) (hΛl : ∀ z ∈ Z, ∀ z' ∈ Z, ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖)
    (hρ : ∀ z ∈ Z, ‖z‖ ≤ ρ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    {a : Eu d → Matrix (Fin d) (Fin d) ℝ} {bb : Eu d → Eu d}
    (hab : ∀ x ∈ S, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka)
    (hah : ∀ x ∈ S, ∀ x' ∈ S, ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧
      ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) :
    (∀ z ∈ Z, ∀ k l, |alTA (DΘ (Λ z)) (a (Λ z)) (a x0) k l| ≤
      Ka * K ^ 2 * (2 * ρ) ^ μ + Ka * (K + 1) * K * ρ) ∧
    (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k l, |alTA (DΘ (Λ z)) (a (Λ z)) (a x0) k l - alTA (DΘ (Λ z')) (a (Λ z')) (a x0) k l| ≤
      Ka * K ^ 2 * ‖z - z'‖ ^ μ + 2 * Ka * K ^ 2 * ‖z - z'‖) ∧
    (∀ z ∈ Z, ∀ k, |betTA (D2Θ (Λ z)) (DΘ (Λ z)) (a (Λ z)) (bb (Λ z)) k| ≤ 2 * Ka * K) ∧
    (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k, |betTA (D2Θ (Λ z)) (DΘ (Λ z)) (a (Λ z)) (bb (Λ z)) k -
      betTA (D2Θ (Λ z')) (DΘ (Λ z')) (a (Λ z')) (bb (Λ z')) k| ≤
      4 * Ka * K * ‖z - z'‖ ^ μ + 2 * Ka * K * ‖z - z'‖) := by
  have hK := hC.hK
  have hKa : 0 ≤ Ka := (norm_nonneg _).trans (hab x0 hx0).2
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0 h0Z)
  have hzt : ∀ z ∈ Z, ∀ z' ∈ Z, ‖Λ z - Λ z'‖ ^ μ ≤ 2 * ‖z - z'‖ ^ μ := fun z hz z' hz' =>
    (Real.rpow_le_rpow (norm_nonneg _) (hΛl z hz z' hz') hμ0).trans (two_rpow_le hμ0 hμ1 (norm_nonneg _))
  have hsa : ∀ x ∈ S, 0 ≤ ∑ i, ∑ j, |a x i j| := fun x _ =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsd : ∀ x x' : Eu d, 0 ≤ ∑ i, ∑ j, |a x i j - a x' i j| := fun x x' =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have tm0 : ∀ z z' : Eu d, 0 ≤ ‖z - z'‖ ^ μ := fun z z' => Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨fun z hz k l => ?_, fun z hz z' hz' k l => ?_, fun z hz k => ?_, fun z hz z' hz' k => ?_⟩
  · have h1 := abs_alTA_sub_le (DΘ (Λ z)) (ContinuousLinearMap.id ℝ (Eu d)) (a (Λ z)) (a x0) (a x0) k l
    rw [alTA_id, sub_zero] at h1
    have hb := hC.b1 _ (hΛS z hz)
    have hid : ‖ContinuousLinearMap.id ℝ (Eu d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hl : ‖Λ z - x0‖ ≤ 2 * ρ := by
      have := hΛl z hz 0 h0Z
      rw [hΛ0, sub_zero] at this
      linarith [hρ z hz]
    have hdiff : ‖DΘ (Λ z) - ContinuousLinearMap.id ℝ (Eu d)‖ ≤ K * (2 * ρ) := by
      rw [← hD0]
      refine (hC.lip1 _ (hΛS z hz) _ hx0).trans ?_
      gcongr
    have ha1 : ∑ i, ∑ j, |a (Λ z) i j - a x0 i j| ≤ Ka * (2 * ρ) ^ μ :=
      (hah _ (hΛS z hz) _ hx0).1.trans (by gcongr)
    have ha0 := (hab x0 hx0).1
    have hX : 0 ≤ Ka * K ^ 2 * (2 * ρ) ^ μ := by positivity
    calc _ ≤ _ := h1
      _ ≤ (1 / 2 : ℝ) * ((Ka * (2 * ρ) ^ μ) * K ^ 2 + Ka * ((K + 1) * (K * (2 * ρ)))) := by
          gcongr
      _ ≤ _ := by linarith
  · have h1 := abs_alTA_sub_le (DΘ (Λ z)) (DΘ (Λ z')) (a (Λ z)) (a (Λ z')) (a x0) k l
    have hb := hC.b1 _ (hΛS z hz)
    have hb' := hC.b1 _ (hΛS z' hz')
    have hl : ‖DΘ (Λ z) - DΘ (Λ z')‖ ≤ K * (2 * ‖z - z'‖) :=
      (hC.lip1 _ (hΛS z hz) _ (hΛS z' hz')).trans (by gcongr; exact hΛl z hz z' hz')
    have ha1 : ∑ i, ∑ j, |a (Λ z) i j - a (Λ z') i j| ≤ Ka * (2 * ‖z - z'‖ ^ μ) :=
      (hah _ (hΛS z hz) _ (hΛS z' hz')).1.trans (by gcongr; exact hzt z hz z' hz')
    have ha0 := (hab _ (hΛS z' hz')).1
    calc _ ≤ _ := h1
      _ ≤ (1 / 2 : ℝ) * ((Ka * (2 * ‖z - z'‖ ^ μ)) * K ^ 2 + Ka * ((K + K) * (K * (2 * ‖z - z'‖)))) := by
          gcongr
      _ = _ := by ring
  · have h1 := abs_betTA_sub_le (D2Θ (Λ z)) 0 (DΘ (Λ z)) 0 (a (Λ z)) 0 (bb (Λ z)) 0 k
    have h0 : betTA (0 : Eu d →L[ℝ] Eu d →L[ℝ] Eu d) (0 : Eu d →L[ℝ] Eu d) (0 : Matrix (Fin d) (Fin d) ℝ)
        (0 : Eu d) k = 0 := by simp [betTA]
    rw [h0, sub_zero] at h1
    simp only [Matrix.zero_apply, sub_zero, abs_zero, Finset.sum_const_zero, zero_mul, add_zero, norm_zero] at h1
    have hb := hC.b1 _ (hΛS z hz)
    have hb2 := hC.b2 _ (hΛS z hz)
    obtain ⟨ha, hbb⟩ := hab _ (hΛS z hz)
    calc _ ≤ _ := h1
      _ ≤ (1 / 2 : ℝ) * (Ka * K) + K * Ka := by
          gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hKa hK]
  · have h1 := abs_betTA_sub_le (D2Θ (Λ z)) (D2Θ (Λ z')) (DΘ (Λ z)) (DΘ (Λ z')) (a (Λ z)) (a (Λ z'))
      (bb (Λ z)) (bb (Λ z')) k
    have hb := hC.b1 _ (hΛS z hz)
    have hb' := hC.b1 _ (hΛS z' hz')
    have hb2 := hC.b2 _ (hΛS z hz)
    have hl : ‖DΘ (Λ z) - DΘ (Λ z')‖ ≤ K * (2 * ‖z - z'‖) :=
      (hC.lip1 _ (hΛS z hz) _ (hΛS z' hz')).trans (by gcongr; exact hΛl z hz z' hz')
    have hh2 : ‖D2Θ (Λ z) - D2Θ (Λ z')‖ ≤ K * (2 * ‖z - z'‖ ^ μ) :=
      (hC.hol2 _ (hΛS z hz) _ (hΛS z' hz')).trans (by gcongr; exact hzt z hz z' hz')
    have ha1 : ∑ i, ∑ j, |a (Λ z) i j - a (Λ z') i j| ≤ Ka * (2 * ‖z - z'‖ ^ μ) :=
      (hah _ (hΛS z hz) _ (hΛS z' hz')).1.trans (by gcongr; exact hzt z hz z' hz')
    have hbd : ‖bb (Λ z) - bb (Λ z')‖ ≤ Ka * (2 * ‖z - z'‖ ^ μ) :=
      (hah _ (hΛS z hz) _ (hΛS z' hz')).2.trans (by gcongr; exact hzt z hz z' hz')
    have ha0 := (hab _ (hΛS z' hz')).1
    have hbb := (hab _ (hΛS z hz)).2
    calc _ ≤ _ := h1
      _ ≤ (1 / 2 : ℝ) * ((Ka * (2 * ‖z - z'‖ ^ μ)) * K + Ka * (K * (2 * ‖z - z'‖ ^ μ))) +
          (K * (2 * ‖z - z'‖) * Ka + K * (Ka * (2 * ‖z - z'‖ ^ μ))) := by
          gcongr
      _ = _ := by ring

end CoefA

section LocalSolveA

variable {d : ℕ}

end LocalSolveA

end ObliqueLib

theorem solution (d : ℕ) (S Z : Set (EuclideanSpace ℝ (Fin d))) (μ K ρ Ka : ℝ) (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (D2Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hC : 0 ≤ K ∧ (∀ x ∈ S, ∀ y ∈ S, ‖Θ x - Θ y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖DΘ x‖ ≤ K) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖DΘ x - DΘ y‖ ≤ K * ‖x - y‖) ∧ (∀ x ∈ S, ‖D2Θ x‖ ≤ K) ∧
      (∀ x ∈ S, ∀ y ∈ S, ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ))
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ S)
    (hD0 : DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) (Λ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΛS : ∀ z ∈ Z, Λ z ∈ S)
    (h0Z : (0 : EuclideanSpace ℝ (Fin d)) ∈ Z) (hΛ0 : Λ 0 = x0) (hΛl : ∀ z ∈ Z, ∀ z' ∈ Z, ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖)
    (hρ : ∀ z ∈ Z, ‖z‖ ≤ ρ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (bb : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hab : ∀ x ∈ S, ∑ i, ∑ j, |a x i j| ≤ Ka ∧ ‖bb x‖ ≤ Ka)
    (hah : ∀ x ∈ S, ∀ x' ∈ S, ∑ i, ∑ j, |a x i j - a x' i j| ≤ Ka * ‖x - x'‖ ^ μ ∧
      ‖bb x - bb x'‖ ≤ Ka * ‖x - x'‖ ^ μ) :
    (∀ z ∈ Z, ∀ k l, |(1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (DΘ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z)) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l)| ≤
      Ka * K ^ 2 * (2 * ρ) ^ μ + Ka * (K + 1) * K * ρ) ∧
    (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k l, |(1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (DΘ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z)) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l) - (1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z')) i j * (DΘ (Λ z')) (EuclideanSpace.single i (1 : ℝ)) k * (DΘ (Λ z')) (EuclideanSpace.single j (1 : ℝ)) l - (a x0) k l)| ≤
      Ka * K ^ 2 * ‖z - z'‖ ^ μ + 2 * Ka * K ^ 2 * ‖z - z'‖) ∧
    (∀ z ∈ Z, ∀ k, |((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (D2Θ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z)) (bb (Λ z)) k)| ≤ 2 * Ka * K) ∧
    (∀ z ∈ Z, ∀ z' ∈ Z, ∀ k, |((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z)) i j * (D2Θ (Λ z)) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z)) (bb (Λ z)) k) -
      ((1 / 2 : ℝ) * (∑ i, ∑ j, (a (Λ z')) i j * (D2Θ (Λ z')) (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) k) + (DΘ (Λ z')) (bb (Λ z')) k)| ≤
      4 * Ka * K * ‖z - z'‖ ^ μ + 2 * Ka * K * ‖z - z'‖) := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hC
  exact ObliqueLib.coef_boundsA ⟨c1, c2, c3, c4, c5, c6⟩ hx0 hD0 hΛS h0Z hΛ0 hΛl hρ hμ0 hμ1 hab hah
