-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Th_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:38:16.822711+00:00
-- url     : https://prove2.me/submissions/252cf5cf-61b1-48d7-90d4-bfbd56342793

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coe_untopD_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullL_coefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_rename_pullL_coefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Th_eq
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_TL_preimage
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_TT_expand
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullE_deg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_range_first_embedding
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_monomial_mem_PolK_sg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_coefOut_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_nonneg_of_free
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_rename
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul_left_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_zero
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_monomial__f1d6e36a6b91
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_sum__e111d2e1e1a9
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_zero__c35e386c5486


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
variable {ι : Type} [Fintype ι]
  (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution [NeZero D.r] {v : AddValuation K (WithTop ℚ)}
    (Ψ : ι → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (path : ι → Fin (D.nB j + D.r + 1) → Fin D.r → ℤ)
    (hli : LinearIndependent K Ψ)
    (hcc : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → monomial lam (1 : K) = ∑ b, cc lam b • Ψ b)
    (h7 : ∀ (th : Fin (D.nB j + D.r + 1) → ℤ) (F : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K),
      (F ∈ PolO v D.r (fun k => D.dO (D.eA j k)) ∧ ∀ i : Fin (D.nB j + D.r + 1),
        F ∈ Aset (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) (th i)) →
        ∃ c : ι → K, (∀ b, 0 ≤ v (c b)) ∧ (∀ b, c b ≠ 0 → ∀ i, th i ≤ path b i (lastIdx D.r)) ∧
          F = ∑ b, c b • Ψ b)
    (hPPval : ∀ b (m : Fin D.r) (i0 : Fin (D.nB j + D.r + 1)), i0.val = D.stg j m →
      ((path b i0 (lastIdx D.r) : ℤ) : WithTop ℤ) ≤ valS D.msg (D.YPset j m) (PP b))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZ : Integral v Z) (hpre : ∀ ζ ∈ Z.support, D.PreE j ζ)
    (m : Fin D.r) (θ : ℝ) (hθ : vala D.msg (D.TLset j m) θ Z) :
    vala D.msg (D.YPset j m) θ (D.Th j cc PP Z) := by
  rw [Th_eq]
  refine vala_sum _ _ fun μ hμ => ?_
  obtain ⟨α0, hα0, rfl⟩ := Finset.mem_image.mp hμ
  refine vala_mul_left_nonneg ?_ ?_
  · apply valS_nonneg_of_free
    intro α hα i hi a
    have h1 := support_monomial_subset hα
    rw [Finset.mem_singleton] at h1
    rw [h1, eOut_apply]
    simp only [YPset, Finset.mem_union, Finset.mem_image] at hi
    rcases hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩
    · rw [if_neg]
      exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))
    · split_ifs
      · exact (hpre α0 hα0).2.2 m' a
      · rfl
  · set Q := D.pullL j (coefOut (D.outSeg j) (eOut (D.outSeg j) α0) Z) with hQdef
    have hQK : Q ∈ PolK K D.r (fun k => D.dO (D.eA j k)) := by
      rw [hQdef, pullL_coefOut]
      refine Submodule.sum_mem _ fun α hα => ?_
      split_ifs
      · exact monomial_mem_PolK_sg _ _ _ (D.pullE_deg j α (hpre α hα))
      · exact Submodule.zero_mem _
    have hQint : Integral v Q := by
      rw [hQdef, pullL_coefOut]
      refine integral_sum' _ _ fun α _ => ?_
      split_ifs
      · exact integral_monomial' _ (hZ α)
      · exact integral_zero'
    have hout : ∀ i ∈ D.TLset j m, ¬ D.outSeg j i := by
      intro i hi
      simp only [TLset, Finset.mem_union, Finset.mem_image] at hi
      rcases hi with ⟨b, hb, rfl⟩ | ⟨m', -, rfl⟩
      · exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inl ⟨b, (Finset.mem_filter.mp hb).2, rfl⟩))
      · exact not_not.mpr ((D.range_first_embedding j _).mpr (Or.inr ⟨m', rfl⟩))
    have hQval : ((⌈θ⌉ : ℤ) : WithTop ℤ) ≤
        valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) (D.stg j m)) Q := by
      have h1 := valS_rename (D.e0 j) (D.index_embedding_injective j) D.msg (D.TLset j m) Q
      rw [hQdef, rename_pullL_coefOut, TL_preimage, ← hQdef] at h1
      rw [← h1]
      exact le_trans ((vala_iff _ _ _ _).mp hθ) (valS_coefOut_le (D.outSeg j) D.msg _ hout _ Z)
    have hlt : D.stg j m < D.nB j + D.r + 1 := by unfold stg; omega
    let i0 : Fin (D.nB j + D.r + 1) := ⟨D.stg j m, hlt⟩
    let th : Fin (D.nB j + D.r + 1) → ℤ := fun i =>
      if i = i0 then ⌈θ⌉ else (valS (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) Q).untopD 0
    have hmem : ∀ i : Fin (D.nB j + D.r + 1),
        Q ∈ Aset (D.msg ∘ D.e0 j) (initSet (D.nB j + D.r) i.val) (th i) := by
      intro i
      show ((th i : ℤ) : WithTop ℤ) ≤ _
      by_cases hi : i = i0
      · simp only [th, if_pos hi]
        rw [hi]
        exact hQval
      · simp only [th, if_neg hi]
        exact coe_untopD_le _
    obtain ⟨c, -, hc1, hc2⟩ := (h7 th Q) ⟨⟨hQK, hQint⟩, hmem⟩
    rw [D.TT_expand j cc PP Ψ hli hcc Q hQK c hc2]
    refine vala_sum _ _ fun b _ => ?_
    by_cases hcb : c b = 0
    · rw [hcb, zero_smul]; exact vala_zero θ
    · refine vala_smul _ ?_
      rw [vala_iff]
      have h2 := hc1 b hcb i0
      simp only [th, if_true] at h2
      exact le_trans (WithTop.coe_le_coe.mpr h2) (hPPval b m i0 rfl)
end Formalism.MainNotions.PlaneGram.TwistData
