-- Prove2me | solution 1 for CuspForm.exists_ne_zero_heckeTLin_eq_smul_heckeULin_eq_of_isNewform_of_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/107c64b0-0fe4-5257-bd4f-5aae9496ee53

import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_Newforms
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeULin_apply_eq_qCoeff_smul
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_ne_zero_heckeTLin_eq_smul_heckeULin_eq_of_isNewform_of_sq_dvd
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open scoped MatrixGroups

namespace O2Refined

theorem factorization_eq_of_dvd_of_not_sq_dvd {M N q : ℕ} (hN : N ≠ 0) (hq : q.Prime) (hMN : M ∣ N)
    (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ N) : N.factorization q = M.factorization q := by
  have hM : M ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hMN))
  have h1 : M.factorization q ≤ N.factorization q := (Nat.factorization_le_iff_dvd hM hN).2 hMN q
  have h2 : 1 ≤ M.factorization q := by
    rw [← hq.pow_dvd_iff_le_factorization hM, pow_one]; exact hqM
  have h3 : N.factorization q < 2 := lt_of_not_ge fun h => hq2 ((hq.pow_dvd_iff_le_factorization hN).2 h)
  omega

theorem sq_dvd_of_factorization_eq {M N q : ℕ} (hN : N ≠ 0) (hq : q.Prime) (hMN : M ∣ N)
    (hq2 : q ^ 2 ∣ N) (heq : ¬ M.factorization q < N.factorization q) : q ^ 2 ∣ M := by
  have hM : M ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hMN))
  have h1 : M.factorization q ≤ N.factorization q := (Nat.factorization_le_iff_dvd hM hN).2 hMN q
  have h2 : 2 ≤ N.factorization q := (hq.pow_dvd_iff_le_factorization hN).1 hq2
  exact (hq.pow_dvd_iff_le_factorization hM).2 (by omega)

end O2Refined

theorem solution
    (N : ℕ) [NeZero N]
    (hN3 : ∀ q : ℕ, q.Prime → ¬ q ^ 3 ∣ N)
    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform)

    (hone : ∀ q : ℕ, q.Prime → q ∣ N → ¬ q ^ 2 ∣ N → q ∣ Mg)

    (hap0 : ∀ q : ℕ, q.Prime → q ^ 2 ∣ Mg → ModularFormClass.qCoeff g q = 0) :
    ∃ g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g' ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        CuspForm.heckeTLin 2 hℓ hℓN g' = (ModularFormClass.qCoeff g ℓ) • g') ∧
      (∀ (q : ℕ), q.Prime → ∀ (hqN : q ∣ N), q ^ 2 ∣ N → CuspForm.heckeULin 2 hqN g' = 0) ∧
      (∀ (q : ℕ), q.Prime → ∀ (hqN : q ∣ N), ¬ q ^ 2 ∣ N →
        CuspForm.heckeULin 2 hqN g' = (ModularFormClass.qCoeff g q) • g') := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨g', hg', hA, hB, -, hD⟩ :=
    CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root (M := Mg) (N := N)
      hMgN hg.isNormalizedEigenform (fun _ => 0)
      (fun q hq hqN hqM hq2 => absurd (hone q hq hqN hq2) hqM)
  refine ⟨g', hg'.ne_zero, ?_, ?_, ?_⟩
  · intro ℓ hℓ hℓN
    rw [CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul N g' hg' ℓ hℓ hℓN, hA ℓ hℓ hℓN]
  · intro q hq hqN hq2
    rw [CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul N g' hg' q hq hqN]
    have h0 : ModularFormClass.qCoeff g' q = 0 := by
      by_cases hlt : Mg.factorization q < N.factorization q
      · exact hD q hq hq2 hlt
      · have hMg2 : q ^ 2 ∣ Mg := O2Refined.sq_dvd_of_factorization_eq hN hq hMgN hq2 hlt
        have hM0 : Mg ≠ 0 := NeZero.ne Mg
        have hle : Mg.factorization q ≤ N.factorization q := (Nat.factorization_le_iff_dvd hM0 hN).2 hMgN q
        rw [hB q hq hqN (by omega), hap0 q hq hMg2]
    rw [h0, zero_smul]
  · intro q hq hqN hq2
    rw [CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul N g' hg' q hq hqN,
      hB q hq hqN (O2Refined.factorization_eq_of_dvd_of_not_sq_dvd hN hq hMgN (hone q hq hqN hq2) hq2)]

end S_CuspForm_exists_ne_zero_heckeTLin_eq_smul_heckeULin_eq_of_isNewform_of_sq_dvd
end P2MW
export P2MW.S_CuspForm_exists_ne_zero_heckeTLin_eq_smul_heckeULin_eq_of_isNewform_of_sq_dvd (solution)
