-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_exists_max_pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:29:39.727808+00:00
-- url     : https://prove2.me/submissions/32acccce-0ee5-4c12-a995-8fe9c93c1672

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaD
import Theorems.Thm_Formalism_UG_P_fIwasawa_col_zero
import Theorems.Thm_Formalism_UG_P_fIwasawa_gram_un
import Theorems.Thm_Formalism_UG_P_fIwasawa_iso
import Theorems.Thm_Formalism_UG_P_fIwasawa_perm
import Theorems.Thm_Formalism_UG_P_fIwasawa_rows
import Theorems.Thm_Formalism_UG_P_permMatrix_isUnitary_of_commute_rev
import Theorems.Thm_P2M_Formalism_UG_P_permMatrix_mul_apply__c01338ce70d6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaUn σ M) (r : ℕ) (hT : fIwasawaTri r M) (ρ : Fin n) (hρr : ρ.val = r)
    (hρ : ρ < Fin.rev ρ) :
    ∃ k, fIwasawaKm σ k ∧ fIwasawaTri r (k * M) ∧ (k * M) ρ ρ ≠ 0 ∧
      ∀ i, ρ ≤ i → i ≤ Fin.rev ρ → Valued.v ((k * M) i ρ) ≤ Valued.v ((k * M) ρ ρ) := by
  classical
  set W : Finset (Fin n) := Finset.univ.filter (fun i => ρ ≤ i ∧ i ≤ Fin.rev ρ) with hW
  have hmem : ∀ i, ρ ≤ i → i ≤ Fin.rev ρ → i ∈ W := fun i h1 h2 =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩
  have hout : ∀ i, i ∉ W → i < ρ ∨ Fin.rev ρ < i := by
    intro i hi
    by_contra h
    push_neg at h
    exact hi (hmem i h.1 h.2)
  have hρW : ρ ∈ W := hmem ρ le_rfl hρ.le
  have hcz := fIwasawa_col_zero σ M hM r hT ρ hρr hρ

  have hex : ∃ j ∈ W, M j ρ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hgram := fIwasawa_gram_un σ M hM (Fin.rev ρ) ρ
    rw [if_pos (Fin.rev_rev ρ).symm] at hgram
    have h0 : ∑ j, σ (M (Fin.rev j) (Fin.rev ρ)) * M j ρ = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj1 : j < ρ
      · have hjr : j.val < r := by rw [← hρr]; exact hj1
        rw [(fIwasawa_rows σ M hM r hT j hjr).2 (Fin.rev ρ) (Fin.rev_lt_rev.2 hj1), map_zero, zero_mul]
      · by_cases hj2 : Fin.rev ρ < j
        · rw [hcz j hj2, mul_zero]
        · rw [hcon j (hmem j (not_lt.1 hj1) (not_lt.1 hj2)), mul_zero]
    rw [h0] at hgram
    exact zero_ne_one hgram
  obtain ⟨j₀, hj₀W, hj₀⟩ := hex
  obtain ⟨a₀, ha₀W, ha₀max⟩ := Finset.exists_max_image W (fun i => Valued.v (M i ρ)) ⟨ρ, hρW⟩
  have hnz : ∀ a ∈ W, (∀ i ∈ W, Valued.v (M i ρ) ≤ Valued.v (M a ρ)) → Valued.v (M a ρ) ≠ 0 := by
    intro a _ hamax h0
    have h1 := hamax j₀ hj₀W
    rw [h0] at h1
    exact hj₀ ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le'))
  have hV := hnz a₀ ha₀W ha₀max
  have hWrev : ∀ j ∈ W, Fin.rev j ∈ W := by
    intro j hj
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.1 hj
    exact hmem _ (by simpa using Fin.rev_le_rev.2 h2) (Fin.rev_le_rev.2 h1)

  obtain ⟨a, haW, hamax, hne⟩ : ∃ a ∈ W, (∀ i ∈ W, Valued.v (M i ρ) ≤ Valued.v (M a ρ)) ∧
      a ≠ Fin.rev a := by
    by_cases h₀ : a₀ = Fin.rev a₀
    · by_contra hcon
      push_neg at hcon
      have hlt : ∀ i ∈ W, i ≠ a₀ → Valued.v (M i ρ) < Valued.v (M a₀ ρ) := by
        intro i hi hia
        refine lt_of_le_of_ne (ha₀max i hi) fun heq => ?_
        have hii : i = Fin.rev i := hcon i hi fun k hk => (ha₀max k hk).trans_eq heq.symm
        apply hia
        have e1 := congrArg Fin.val hii
        have e2 := congrArg Fin.val h₀
        rw [Fin.val_rev] at e1 e2
        exact Fin.ext (by omega)
      have hiso := fIwasawa_iso σ M hM ρ hρ
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a₀)] at hiso
      have hbig : Valued.v (σ (M (Fin.rev a₀) ρ) * M a₀ ρ) = Valued.v (M a₀ ρ) * Valued.v (M a₀ ρ) := by
        rw [← h₀, map_mul, hσv]
      have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v (M a₀ ρ) * Valued.v (M a₀ ρ) :=
        zero_lt_iff.2 (mul_ne_zero hV hV)
      have hsmall : Valued.v (∑ j ∈ Finset.univ.erase a₀, σ (M (Fin.rev j) ρ) * M j ρ)
          < Valued.v (M a₀ ρ) * Valued.v (M a₀ ρ) := by
        apply Valuation.map_sum_lt _ (mul_ne_zero hV hV)
        intro j hj
        have hja := Finset.ne_of_mem_erase hj
        rw [map_mul, hσv]
        by_cases hjW : j ∈ W
        · have hra : Fin.rev j ≠ a₀ := by
            intro h; apply hja; rw [← Fin.rev_rev j, h, ← h₀]
          exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (ha₀max _ (hWrev j hjW)) (hlt j hjW hja)
            zero_le' (zero_lt_iff.2 hV)
        · rcases hout j hjW with h | h
          · rw [hcz (Fin.rev j) (Fin.rev_lt_rev.2 h), map_zero, zero_mul]; exact hpos
          · rw [hcz j h, map_zero, mul_zero]; exact hpos
      have h3 : σ (M (Fin.rev a₀) ρ) * M a₀ ρ = -∑ j ∈ Finset.univ.erase a₀, σ (M (Fin.rev j) ρ) * M j ρ :=
        eq_neg_of_add_eq_zero_left hiso
      rw [h3, Valuation.map_neg] at hbig
      rw [hbig] at hsmall
      exact lt_irrefl _ hsmall
    · exact ⟨a₀, ha₀W, ha₀max, h₀⟩
  have haW' := Finset.mem_filter.1 haW
  obtain ⟨π, hπa, hπrev, hπfix⟩ := fIwasawa_perm ρ a hρ haW'.2.1 haW'.2.2 hne
  have hπW : ∀ i ∈ W, π i ∈ W := by
    intro i hi
    by_contra hni
    have hii : π i = i := π.injective (hπfix (π i) (hout _ hni))
    rw [hii] at hni
    exact hni hi
  have hInt : fIwasawaInt (fIwasawaP (L := L) π) := by
    intro i j
    simp only [fIwasawaP, Matrix.of_apply]
    split_ifs <;> simp
  refine ⟨fIwasawaP π, ⟨permMatrix_isUnitary_of_commute_rev σ π hπrev, hInt⟩, ?_, ?_, ?_⟩
  · intro i j hj hji
    rw [permMatrix_mul_apply₂]
    by_cases hiW : i ∈ W
    · have hπi := Finset.mem_filter.1 (hπW i hiW)
      have hjρ : j < ρ := by rw [Fin.lt_iff_val_lt_val, hρr]; exact hj
      exact hT (π i) j hj (lt_of_lt_of_le hjρ hπi.2.1)
    · rw [hπfix i (hout i hiW)]
      exact hT i j hj hji
  · rw [permMatrix_mul_apply₂, hπa]
    intro h0
    exact hnz a haW hamax (by rw [h0, map_zero])
  · intro i h1 h2
    rw [permMatrix_mul_apply₂, permMatrix_mul_apply₂, hπa]
    exact hamax (π i) (hπW i (hmem i h1 h2))
end Formalism.UG.P
