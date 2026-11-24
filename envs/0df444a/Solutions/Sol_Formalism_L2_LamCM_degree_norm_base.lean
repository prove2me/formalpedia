-- Prove2me | solution 1 for Formalism.L2.LamCM.degree_norm_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:18.694907+00:00
-- url     : https://prove2.me/submissions/eb5873fb-04e2-487b-8725-e01ec4b57743

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
import Theorems.Thm_Formalism_L2_LamCM_finrank_pos_real
import Theorems.Thm_Formalism_L2_LamCM_degree_delta_base
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
private lemma mLine_deg_dual {K : Type} [Field K] [NumberField K] (L : MLine K) : L.dual.deg = - L.deg := by
  simp only [MLine.deg, MLine.dual, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
  ring
private lemma mLine_good_pow {K : Type} [Field K] [NumberField K] (L : MLine K) (hL : L.Good) (k : ℕ) :
    (L.pow k).Good := by
  unfold MLine.Good at *
  exact ⟨pow_ne_zero _ hL.1, fun σ => pow_pos (hL.2 σ) _⟩
private lemma mLine_good_dual {K : Type} [Field K] [NumberField K] (L : MLine K) (hL : L.Good) : L.dual.Good := by
  unfold MLine.Good at *
  exact ⟨inv_ne_zero hL.1, fun σ => inv_pos.mpr (hL.2 σ)⟩
private lemma mLine_good_tensor {K : Type} [Field K] [NumberField K] (L M : MLine K) (hL : L.Good) (hM : M.Good) :
    (L.tensor M).Good := by
  unfold MLine.Good at *
  exact ⟨mul_ne_zero hL.1 hM.1, fun σ => mul_pos (hL.2 σ) (hM.2 σ)⟩
private lemma mLine_good_prodPow {K : Type} [Field K] [NumberField K] {V : Type} [Fintype V] (ℓ : V → MLine K)
    (k : V → ℕ) (h : ∀ v, (ℓ v).Good) : (MLine.prodPow ℓ k).Good := by
  unfold MLine.Good at *
  exact ⟨Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (h v).1,
    fun σ => Finset.prod_pos fun v _ => pow_pos ((h v).2 σ) _⟩
private lemma mLine_deg_tensor {K : Type} [Field K] [NumberField K] (L M : MLine K) (hL : L.Good) (hM : M.Good) :
    (L.tensor M).deg = L.deg + M.deg := by
  have hL0 : ((FractionalIdeal.absNorm L.I : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ((map_ne_zero _).mpr hL.1)
  have hM0 : ((FractionalIdeal.absNorm M.I : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ((map_ne_zero _).mpr hM.1)
  simp only [MLine.deg, MLine.tensor, map_mul, Rat.cast_mul]
  rw [Real.log_mul hL0 hM0, Finset.sum_congr rfl (fun σ _ => Real.log_mul (hL.2 σ).ne' (hM.2 σ).ne'),
    Finset.sum_add_distrib]
  ring
private lemma mLine_deg_pow {K : Type} [Field K] [NumberField K] (L : MLine K) (k : ℕ) :
    (L.pow k).deg = k * L.deg := by
  simp only [MLine.deg, MLine.pow, map_pow, Rat.cast_pow, Real.log_pow]
  rw [mul_sub, Finset.mul_sum]
  ring
private lemma mLine_deg_prodPow {K : Type} [Field K] [NumberField K] {V : Type} [Fintype V] (ℓ : V → MLine K)
    (k : V → ℕ) (h : ∀ v, (ℓ v).Good) : (MLine.prodPow ℓ k).deg = ∑ v, (k v : ℝ) * (ℓ v).deg := by
  have hN : ∀ v, ((FractionalIdeal.absNorm (ℓ v).I : ℚ) : ℝ) ≠ 0 := fun v =>
    Rat.cast_ne_zero.mpr ((map_ne_zero _).mpr (h v).1)
  simp only [MLine.deg, MLine.prodPow, map_prod, map_pow, Rat.cast_prod, Rat.cast_pow]
  rw [Real.log_prod (fun v _ => pow_ne_zero _ (hN v))]
  rw [Finset.sum_congr rfl (fun σ _ => Real.log_prod (fun v _ => (pow_pos ((h v).2 σ) _).ne'))]
  simp only [Real.log_pow]
  rw [Finset.sum_comm]
  simp only [mul_sub, mul_neg, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
section cauchy
end cauchy
section loc
variable {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}
end loc
section galois
variable {K : Type} [Field K] [NumberField K]
end galois
end Formalism.L2.LamCM
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace Formalism.L2.LamCM
theorem _root_.solution : DegNN0 := by
  unfold DegNN0
  intro K _ _ g abelian₂ ℓ de La logOm V _ c μ n h
  have hde0 := degree_delta_base K g abelian₂ ℓ de La logOm h
  unfold CMNumbers0 at h
  obtain ⟨-, hℓ, hde, hLa, -, hnd, -⟩ := h
  have hP : (MLine.prodPow (fun v => ℓ (c v)) μ).Good := mLine_good_prodPow _ _ (fun v => hℓ (c v))
  have hPd : (MLine.prodPow (fun v => ℓ (c v)) μ).dual.Good := mLine_good_dual _ hP
  have hdn : (de.pow n).Good := mLine_good_pow _ hde n
  have hG : (lineNN de ℓ c μ n).Good := mLine_good_tensor _ _ hdn hPd
  refine ⟨hG, ?_⟩
  have hd : (0:ℝ) < (Module.finrank ℚ K : ℝ) := finrank_pos_real K
  have hd0 : (Module.finrank ℚ K : ℝ) ≠ 0 := hd.ne'
  have hdeg : ∀ j, (ℓ j).deg = logOm / 2 * (Module.finrank ℚ K : ℝ) := fun j => by
    have e : (ℓ j).ndeg = (ℓ j).deg / (Module.finrank ℚ K : ℝ) := rfl
    rw [← hnd j, e, div_mul_cancel₀ _ hd0]
  have hD : (lineNN de ℓ c μ n).deg =
      n * de.deg - (∑ v, (μ v : ℝ)) * (logOm / 2 * (Module.finrank ℚ K : ℝ)) := by
    have e : lineNN de ℓ c μ n = (de.pow n).tensor (MLine.prodPow (fun v => ℓ (c v)) μ).dual := rfl
    rw [e, mLine_deg_tensor _ _ hdn hPd, mLine_deg_dual, mLine_deg_pow, mLine_deg_prodPow _ _ (fun v => hℓ (c v))]
    simp only [hdeg, Finset.sum_mul]
    ring
  have hlog : 0 ≤ Real.log La := Real.log_nonneg hLa
  have hPl : -(logOm / 2) ≤ pDeg logOm + (1 / 2) * Real.log La := by
    unfold pDeg
    have := neg_le_abs logOm
    linarith
  have hsμ : (0:ℝ) ≤ ∑ v, (μ v : ℝ) := Finset.sum_nonneg (fun v _ => Nat.cast_nonneg _)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (n:ℝ) * de.ndeg ≤ n * (g * (pDeg logOm + (1 / 2) * Real.log La)) := mul_le_mul_of_nonneg_left hde0 hn
  have h2 : (∑ v, (μ v : ℝ)) * (-(logOm / 2)) ≤ (∑ v, (μ v : ℝ)) * (pDeg logOm + (1 / 2) * Real.log La) :=
    mul_le_mul_of_nonneg_left hPl hsμ
  have e2 : (lineNN de ℓ c μ n).ndeg = (lineNN de ℓ c μ n).deg / (Module.finrank ℚ K : ℝ) := rfl
  have e3 : de.ndeg = de.deg / (Module.finrank ℚ K : ℝ) := rfl
  have hnd' : (lineNN de ℓ c μ n).ndeg = n * de.ndeg - (∑ v, (μ v : ℝ)) * (logOm / 2) := by
    rw [e2, e3, hD, sub_div, mul_div_assoc]
    congr 1
    field_simp
  rw [hnd']
  linarith
end Formalism.L2.LamCM
