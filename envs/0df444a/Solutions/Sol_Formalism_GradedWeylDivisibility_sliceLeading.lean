-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.sliceLeading
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:10.927398+00:00
-- url     : https://prove2.me/submissions/8e97d3f5-4e4b-4407-a1c5-a4df73a8980e

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCpleadLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_PeelLead
import Theorems.Thm_Formalism_GradedWeylDivisibility_colLex_lt_iff
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_cmIdx_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_coeff_peel
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_hom_off
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_hom_row
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_mem_support_peel
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcplead_recon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
open scoped MonomialOrder
noncomputable section
namespace Formalism.GradedWeylDivisibility
private theorem toLex_lt_of_eq_of_lt_at {N : ℕ} {a b : Fin N →₀ ℕ} (i : Fin N)
    (h1 : ∀ i', i' < i → a i' = b i') (h2 : a i < b i) : toLex a < toLex b := by
  first
  | exact Finsupp.lex_lt_iff.2 ⟨i, h1, h2⟩
  | exact Finsupp.lex_def.2 ⟨i, h1, h2⟩
  | exact ⟨i, h1, h2⟩
private theorem domCongr_cmIdx_apply_eq {r n : ℕ} (m : Fin r × Fin n →₀ ℕ)
    (x : Fin r × Fin n) :
    Finsupp.domCongr (cmIdx r n) m (cmIdx r n x) = m x := by
  first
  | (simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)
  | (simp [Finsupp.domCongr_apply]; done)
  | rfl
private theorem toSyn_le_toSyn_degree_of_mem_support {σ R : Type*} [CommSemiring R] (M : MonomialOrder σ)
    {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    M.toSyn d ≤ M.toSyn (M.degree f) := by
  first
  | exact M.le_degree hd
  | (unfold MonomialOrder.degree; rw [AddEquiv.apply_symm_apply]; exact Finset.le_sup hd)
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
open scoped MonomialOrder
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : PeelLead := by
  unfold PeelLead
  intro B _ _ r n l j hlj a0 ω g K hg hω hK htop
  have hlj' : l ≠ j := ne_of_lt hlj
  have hd : (colLex r n).degree (peel l j a0 K g) ∈
      (peel l j a0 K g).support :=
    (colLex r n).degree_mem_support hK
  obtain ⟨m0, hm0, hm0K, hd_eq⟩ := lcplead_mem_support_peel a0 K hd
  have hm0_eq := lcplead_recon hlj' a0 hg hm0
  rw [hm0K, ← hd_eq] at hm0_eq
  rw [← hm0_eq]
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hm0
  have hup : ∀ m ∈ g.support, (colLex r n).toSyn m ≤ (colLex r n).toSyn m0 := by
    intro m hm
    rcases lt_trichotomy (m (a0, l)) K with hlt | heq | hgt
    · apply le_of_lt
      apply colLex_lt_iff.2
      refine toLex_lt_of_eq_of_lt_at (cmIdx r n (a0, l)) ?_ ?_
      · intro i' hi'
        obtain ⟨⟨b, t⟩, rfl⟩ := (cmIdx r n).surjective i'
        rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq]
        rcases lcplead_cmIdx_lt hi' with ht | ⟨ht, hb⟩
        · have htl : t ≠ l := ne_of_lt ht
          have htj : t ≠ j := ne_of_lt (lt_trans ht hlj)
          rw [lcplead_hom_off hlj' hg hm b t htl htj,
            lcplead_hom_off hlj' hg hm0 b t htl htj]
        · rw [ht]
          have h1 := lcplead_hom_row hlj' hg hm b
          have h2 := lcplead_hom_row hlj' hg hm0 b
          have h3 := hω b hb
          omega
      · rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq, hm0K]
        exact hlt
    · have hc := lcplead_coeff_peel hlj' a0 hg hm
      rw [heq] at hc
      have he : (m.erase (a0, l)).erase (a0, j) ∈ (peel l j a0 K g).support := by
        rw [mem_support_iff, hc]
        exact mem_support_iff.1 hm
      have hle := toSyn_le_toSyn_degree_of_mem_support (colLex r n) he
      have hm_eq := lcplead_recon hlj' a0 hg hm
      rw [heq] at hm_eq
      rw [hm_eq, hm0_eq]
      simp only [map_add]
      first
      | exact add_le_add le_rfl hle
      | exact add_le_add_left hle _
      | gcongr
    · exfalso
      have hc := lcplead_coeff_peel hlj' a0 hg hm
      rw [htop _ hgt, coeff_zero] at hc
      exact mem_support_iff.1 hm hc.symm
  exact (colLex r n).toSyn.injective
    (le_antisymm (hup _ ((colLex r n).degree_mem_support hg0))
      (toSyn_le_toSyn_degree_of_mem_support (colLex r n) hm0))
end Formalism.GradedWeylDivisibility
