-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2_tau_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:36.004375+00:00
-- url     : https://prove2.me/submissions/edc28a9c-efd4-40b3-bcb4-027518df0537

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_hzz_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_uMap_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_mulVec_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_X_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_X_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_nEich_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_nEich_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_xiV_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_xiV_apply_last_block_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_col_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_unipotent_apply_middle_column

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector UnipotentSums
private lemma mul_mem_Nset' {k r : ℕ} {A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hA : A ∈ Nset k r) (hB : B ∈ Nset k r) : A * B ∈ Nset k r := by
  obtain ⟨hAu, hAc, hAw⟩ := hA
  obtain ⟨hBu, hBc, hBw⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · have hAu' : Aᴴ * Hpk k r * A = Hpk k r := hAu
    have hBu' : Bᴴ * Hpk k r * B = Hpk k r := hBu
    show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
    rw [Matrix.conjTranspose_mul,
      show Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B by
        simp only [Matrix.mul_assoc], hAu', hBu']
  · intro a i hai
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
    · rw [hBc a (eI k r a) (le_refl a.val), if_pos rfl, mul_one]
      exact hAc a i hai
    · intro j _ hj
      by_cases hja : a.val ≤ j.val
      · rw [hBc a j hja, if_neg hj, mul_zero]
      · rw [not_le] at hja
        have hjr : j.val < r := lt_trans hja a.isLt
        have h1 := hAc ⟨j.val, hjr⟩ i (show j.val ≤ i.val by omega)
        rw [show eI k r ⟨j.val, hjr⟩ = j from Fin.ext rfl] at h1
        rw [h1, if_neg (by rintro rfl; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i j hj1 hj2 hi
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hBw j j hj1 hj2 hj1, if_pos rfl, mul_one]
      exact hAw i j hj1 hj2 hi
    · intro l _ hl
      by_cases hlr : r ≤ l.val
      · rw [hBw l j hj1 hj2 hlr, if_neg hl, mul_zero]
      · rw [not_le] at hlr
        have h1 := hAc ⟨l.val, hlr⟩ i (show l.val ≤ i.val by omega)
        rw [show eI k r ⟨l.val, hlr⟩ = l from Fin.ext rfl] at h1
        rw [h1, if_neg (by rintro rfl; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
private lemma dite_lt_eq_sum_smul_bvec {k r : ℕ} (g : Fin r → ℂ) :
    (fun p : Fin (2 * r + k + 1) => if hp : p.val < r then g ⟨p.val, hp⟩ else 0) =
      ∑ c, g c • bvec (eI k r c) := by
  funext p
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, bvec, smul_eq_mul, Pi.single_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single ⟨p.val, hp⟩]
    · rw [if_pos (show p = eI k r ⟨p.val, hp⟩ from Fin.ext rfl), mul_one]
    · intro c _ hc
      rw [if_neg, mul_zero]
      intro h
      apply hc
      apply Fin.ext
      show c.val = p.val
      rw [h]
      rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg, mul_zero]
    intro h
    apply hp
    rw [h]
    exact c.isLt
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector UnipotentSums
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.TauMem := by
  intro k r z hz v hv
  set ξ : Fin r → ℂ := fun a => v a.castSucc (Fin.last r) with hξ
  set vX := v.submatrix Fin.castSucc Fin.castSucc with hvX
  have htau : C2.tauM k r z v = C2.nEich k r z ξ * C2.mX k r vX := rfl
  have hvX_mem : vX ∈ C2.UTset r :=
    ⟨fun i j hij => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij), fun i => hv.2 _⟩
  have hzW : ∀ i : Fin (2 * r + k + 1), r + k < i.val → z i = 0 := fun i hi => hz.1 i (Or.inr hi)
  have hxi : C2.xiV k r ξ = ∑ c, ξ c • bvec (eI k r c) := by
    rw [← dite_lt_eq_sum_smul_bvec]
    rfl
  have hfc : ∀ c : Fin r, fvec k r z c.castSucc = bvec (eI k r c) := by
    intro c
    simp [fvec]
  have hfl : fvec k r z (Fin.last r) = z := by
    simp [fvec]
  have hact : ∀ b, C2.tauM k r z v *ᵥ fvec k r z b = ∑ a, v a b • fvec k r z a := by
    intro b
    rw [htau, ← Matrix.mulVec_mulVec, Fin.sum_univ_castSucc]
    simp only [hfc, hfl]
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · have hmz : C2.mX k r vX *ᵥ z = z := by
        funext p
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single p]
        · by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
          · rw [unipotent_apply_middle_column vX p p hp.1 hp.2, if_pos rfl, one_mul]
          · have : z p = 0 := by
              apply hz.1
              omega
            rw [this, mul_zero]
        · intro j _ hj
          by_cases hjW : r ≤ j.val ∧ j.val ≤ r + k
          · rw [unipotent_apply_middle_column vX p j hjW.1 hjW.2, if_neg (Ne.symm hj), zero_mul]
          · have : z j = 0 := by
              apply hz.1
              omega
            rw [this, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hfl, hmz, HermitianXiVector.nEich_apply]
      have h1 : herm (Hpk k r) z (C2.xiV k r ξ) = 0 :=
        HermitianXiVector.herm_X_right (C2.xiV k r ξ) z (HermitianXiVector.xiV_X ξ) hzW
      have h2 : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := hzz_real z
      have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hz.2)
      have hll : v (Fin.last r) (Fin.last r) = 1 := hv.2 _
      rw [h1, h2, hll, one_smul, ← hxi]
      have : ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) * (-(((-(Tz k r z) : ℝ) : ℂ))) = 1 := by
        push_cast
        field_simp
      rw [zero_smul, mul_zero, zero_smul, add_zero, add_zero, smul_smul, this, one_smul]
      exact add_comm _ _
    · have hmy : C2.mX k r vX *ᵥ bvec (eI k r b') =
          fun p => if hp : p.val < r then vX ⟨p.val, hp⟩ b' else 0 := by
        rw [FlagSpanVanishing.mulVec_bvec]
        funext p
        exact mX_col_X vX p b'
      have hyX : ∀ i : Fin (2 * r + k + 1), r ≤ i.val →
          (fun p : Fin (2 * r + k + 1) => if hp : p.val < r then vX ⟨p.val, hp⟩ b' else 0) i = 0 := by
        intro i hi
        simp only
        rw [dif_neg (by omega)]
      have h1 := HermitianXiVector.herm_X_left _ z hyX hzW
      have h2 := HermitianXiVector.herm_X_left _ (C2.xiV k r ξ) hyX (HermitianXiVector.xiV_apply_last_block_zero ξ)
      have hlow : v (Fin.last r) b'.castSucc = 0 := hv.1 _ _ (Fin.castSucc_lt_last b')
      rw [hfc, hmy, HermitianXiVector.nEich_apply, h1, h2, hlow, zero_smul, add_zero]
      simp only [neg_zero, zero_smul, mul_zero, add_zero, smul_zero]
      exact (dite_lt_eq_sum_smul_bvec (k := k) (fun c => vX c b')).trans rfl
  refine ⟨?_, hact, uMap_eq hz _ v hact⟩
  rw [htau]
  exact mul_mem_Nset' (HermitianXiVector.nEich_mem hz ξ) (mX_mem vX hvX_mem)
end Formalism.FourierDecayAlt.P
