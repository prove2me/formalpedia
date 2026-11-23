-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.monoShapeLow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:23.980727+00:00
-- url     : https://prove2.me/submissions/30a62ab3-e31a-40d9-ace1-7df466979c43

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAOneMonomialLogLoss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mono
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mono
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
namespace Formalism.DworkPowerSeriesWeights
private lemma exists_coeff_ne_zero_of_coeff_prod_ne_zero {ι σ R : Type*} [CommRing R] (s : Finset ι) (f : ι → MvPolynomial σ R) :
    ∀ d : σ →₀ ℕ, MvPolynomial.coeff d (∏ i ∈ s, f i) ≠ 0 →
      ∃ g : ι → σ →₀ ℕ, (∀ i ∈ s, MvPolynomial.coeff (g i) (f i) ≠ 0) ∧ d = ∑ i ∈ s, g i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro d h
    refine ⟨fun _ => 0, fun i hi => by simp at hi, ?_⟩
    rw [Finset.prod_empty, MvPolynomial.coeff_one] at h
    rw [Finset.sum_empty]
    by_contra hd
    exact h (if_neg (Ne.symm hd))
  · intro a t ha ih d h
    rw [Finset.prod_insert ha, MvPolynomial.coeff_mul] at h
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨g, hg, hgd⟩ := ih x.2 (right_ne_zero_of_mul hne)
    refine ⟨fun i => if i = a then x.1 else g i, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · simpa using left_ne_zero_of_mul hne
      · have hia : i ≠ a := fun h => ha (h ▸ hi')
        simpa [hia] using hg i hi'
    · have h2 : ∑ i ∈ t, (if i = a then x.1 else g i) = ∑ i ∈ t, g i :=
        Finset.sum_congr rfl fun i hi => if_neg (show i ≠ a from fun h => ha (h ▸ hi))
      calc d = x.1 + x.2 := (Finset.HasAntidiagonal.mem_antidiagonal.1 hx).symm
        _ = x.1 + ∑ i ∈ t, g i := by rw [hgd]
        _ = _ := by rw [Finset.sum_insert ha, h2]; simp
private lemma exists_injective_perm_of_coeff_det_ne_zero {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J] {N1 n : ℕ}
    (a : Fin n → J → R) (I : Fin n → Fin N1) (d : J × Fin N1 →₀ ℕ)
    (h : MvPolynomial.coeff d (Matrix.of fun (r r' : Fin n) =>
      ∑ j, MvPolynomial.C (a r j) * (MvPolynomial.X (j, I r') : MvPolynomial (J × Fin N1) R)).det ≠ 0) :
    ∃ κ : Fin n → J, Function.Injective κ ∧ (∃ σ : Equiv.Perm (Fin n), ∀ i, a (σ i) (κ i) ≠ 0) ∧
      d = ∑ i, Finsupp.single (κ i, I i) 1 := by
  classical
  have key : (Matrix.of fun (r r' : Fin n) =>
      ∑ j, MvPolynomial.C (a r j) * (MvPolynomial.X (j, I r') : MvPolynomial (J × Fin N1) R)).det =
      ∑ κ : Fin n → J, MvPolynomial.C (Matrix.of fun (r i : Fin n) => a r (κ i)).det *
        ∏ i, (MvPolynomial.X (κ i, I i) : MvPolynomial (J × Fin N1) R) := by
    rw [Matrix.det_apply]
    simp only [Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Matrix.det_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply, Finset.prod_mul_distrib, map_prod, Units.smul_def, map_zsmul,
      smul_mul_assoc]
  rw [key, MvPolynomial.coeff_sum] at h
  obtain ⟨κ, -, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hX : ∏ i, (MvPolynomial.X (κ i, I i) : MvPolynomial (J × Fin N1) R) =
      MvPolynomial.monomial (∑ i, Finsupp.single (κ i, I i) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]; rfl
  rw [hX, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial] at hκ
  by_cases hd : (∑ i, Finsupp.single (κ i, I i) 1 : J × Fin N1 →₀ ℕ) = d
  · rw [if_pos hd, mul_one] at hκ
    refine ⟨κ, ?_, ?_, hd.symm⟩
    · intro i j hij
      by_contra hne
      exact hκ (Matrix.det_zero_of_column_eq hne fun r => by simp [hij])
    · rw [Matrix.det_apply] at hκ
      obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hκ
      refine ⟨σ, fun i hi => hσ ?_⟩
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi), smul_zero]
  · rw [if_neg hd, mul_zero] at hκ
    exact absurd rfl hκ
private lemma sum_single_pair_apply_eq_card_filter {J : Type*} [DecidableEq J] {N1 n : ℕ} (κ : Fin n → J) (I : Fin n → Fin N1)
    (j : J) :
    ∑ b : Fin N1, (∑ i, Finsupp.single (κ i, I i) 1 : J × Fin N1 →₀ ℕ) (j, b) =
      (Finset.univ.filter fun i => κ i = j).card := by
  rw [Finset.card_filter]
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : κ i = j <;> simp [h, Prod.ext_iff]
end Formalism.DworkPowerSeriesWeights
end

set_option autoImplicit false
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : MonoShapeLow.{u} := by
  unfold MonoShapeLow
  intro R _ N0 N1 m C T p hp I mono hmono
  classical
  rw [MvPolynomial.mem_support_iff] at hmono
  unfold minorProd at hmono
  obtain ⟨g, hg, hmg⟩ := exists_coeff_ne_zero_of_coeff_prod_ne_zero Finset.univ _ mono hmono
  have hc : ∀ c, (∑ k : Fin m, ∑ b : Fin N1, g c (k, b)) = p c ∧
      ∀ k, ∑ b : Fin N1, g c (k, b) ≤ 1 := by
    intro c
    obtain ⟨κ, hκ, -, hd⟩ := exists_injective_perm_of_coeff_det_ne_zero
      (fun (r : Fin (p c)) (k : Fin m) => T ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ k) (I c) (g c)
      (hg c (Finset.mem_univ c))
    rw [hd]
    simp only [sum_single_pair_apply_eq_card_filter]
    refine ⟨?_, fun k => ?_⟩
    · rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
    · exact Finset.card_le_one.2 fun i hi j hj =>
        hκ ((Finset.mem_filter.1 hi).2.trans (Finset.mem_filter.1 hj).2.symm)
  have hsum : ∀ k, ∑ b : Fin N1, mono (k, b) = ∑ c, ∑ b : Fin N1, g c (k, b) := by
    intro k
    rw [hmg]
    simp only [Finsupp.finset_sum_apply]
    exact Finset.sum_comm
  refine ⟨?_, fun k => ?_⟩
  · simp only [hsum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => (hc c).1
  · rw [hsum]
    calc ∑ c, ∑ b : Fin N1, g c (k, b) ≤ ∑ _c : Fin C, 1 :=
          Finset.sum_le_sum fun c _ => (hc c).2 k
      _ = C := by simp
end Formalism.DworkPowerSeriesWeights
