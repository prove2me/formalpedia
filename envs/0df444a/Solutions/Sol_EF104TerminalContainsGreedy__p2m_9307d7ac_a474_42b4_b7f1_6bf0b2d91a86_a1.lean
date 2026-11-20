-- Prove2me | solution 1 for EF104TerminalContainsGreedy__p2m_9307d7ac_a474_42b4_b7f1_6bf0b2d91a86_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-19T15:25:09.962099+00:00
-- url     : https://prove2.me/submissions/a356558f-be3f-47f5-a91b-7ab369813056

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Definitions.Def_EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
import Theorems.Thm_EnvyFreeCake104_Divide_valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
import Theorems.Thm_EnvyFreeCake104_Divide_ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1

open EnvyFreeCake104.Divide

set_option autoImplicit false

private lemma value_mono__p2m_a1a978aa_d041_4b6b_9848_fe8a8c0ddba8_a1
    (v : Valuation) {S T : Set ℝ} (hST : S ⊆ T) : v.value S ≤ v.value T := by
  unfold Valuation.value
  apply MeasureTheory.setIntegral_mono_set
    (v.integrable.mono_set Set.inter_subset_right)
  · exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc v.nonneg)
  · exact Filter.Eventually.of_forall (fun x hx ↦ ⟨hST hx.1, hx.2⟩)

private lemma suffix_comparable__p2m_a1a978aa_d041_4b6b_9848_fe8a8c0ddba8_a1
    (Q : Piece) {S T : Set ℝ} (hS : IsSuffix S Q) (hT : IsSuffix T Q) :
    S ⊆ T ∨ T ⊆ S := by
  rcases hS with rfl | ⟨p, hp, rfl⟩
  · exact Or.inl (Set.empty_subset _)
  rcases hT with rfl | ⟨q, hq, rfl⟩
  · exact Or.inr (Set.empty_subset _)
  by_cases hpq : p.1 < q.1
  · exact Or.inr
      (valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
        Q p q hp hq (Or.inl hpq))
  by_cases hqp : q.1 < p.1
  · exact Or.inl
      (valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
        Q q p hq hp (Or.inl hqp))
  have he : p.1 = q.1 := by omega
  rcases le_total p.2 q.2 with h | h
  · exact Or.inr
      (valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
        Q p q hp hq (Or.inr ⟨he, h⟩))
  · exact Or.inl
      (valid_suffix_antitone__p2m_4f88c27f_5aff_4766_80c5_ebd56db53b44_a1
        Q q p hq hp (Or.inr ⟨he.symm, h⟩))

theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (g : List ι × List ι) (hg : g ∈ guesses N)
    (A X : ι → Set ℝ)
    (hA : EF104GreedyProfile__p2m_e30dcdf5_697c_4dac_9565_d07a1e730ebe_a1
      V P g.1 g.2 A)
    (hX : ∀ p ∈ g.1.zip g.2, IsSuffix (X p.1) (P p.2))
    (hstop :
    ∀ (before : List (ι × ι)) (p : ι × ι) (after : List (ι × ι)),
      g.1.zip g.2 = before ++ p :: after →
        X p.1 = (P p.2).toSet ∨
        ∃ q ∈ before, (V q.1).value (X q.1) < (V q.1).value (X p.1)) :
    ∀ i ∈ N, A i ⊆ X i := by
  classical
  have hgmem : g.1 ∈ N.toList.permutations ∧ g.2 ∈ N.toList.permutations := by
    exact List.mem_product.mp hg
  have hag : g.1.Perm N.toList := List.perm_of_mem_permutations hgmem.1
  have hpc : g.2.Perm N.toList := List.perm_of_mem_permutations hgmem.2
  have hlen : g.1.length = g.2.length := hag.length_eq.trans hpc.length_eq.symm
  have hpiece : ∀ p ∈ g.1.zip g.2, (P p.2).WF := by
    intro p hp
    apply hP p.2
    have hm := hpc.mem_iff.mp (List.of_mem_zip hp).2
    simpa using hm
  have advance : ∀ (rest before : List (ι × ι)),
      g.1.zip g.2 = before ++ rest →
      (∀ q ∈ before, A q.1 ⊆ X q.1) →
      ∀ p ∈ rest, A p.1 ⊆ X p.1 := by
    intro rest
    induction rest with
    | nil =>
        intro before heq hind p hp
        simp at hp
    | cons p rest ih =>
        intro before heq hind
        have hp : p ∈ g.1.zip g.2 := by
          rw [heq]
          simp
        have hgreedy := hA before p rest heq
        have hcontain : A p.1 ⊆ X p.1 := by
          rcases hstop before p rest heq with hwhole | ⟨q, hq, henvy⟩
          · rw [hwhole]
            exact (ordered_suffix_calculus__p2m_e0d664ca_af16_41d5_85cd_aa65459b7f06_a1
              (P p.2) (hpiece p hp)).2.1 (A p.1) hgreedy.1
          · rcases suffix_comparable__p2m_a1a978aa_d041_4b6b_9848_fe8a8c0ddba8_a1
                (P p.2) hgreedy.1 (hX p hp) with hgood | hreverse
            · exact hgood
            · have hbound : (V q.1).value (X p.1) ≤ (V q.1).value (X q.1) :=
                (value_mono__p2m_a1a978aa_d041_4b6b_9848_fe8a8c0ddba8_a1
                  (V q.1) hreverse).trans
                  ((hgreedy.2.1 q hq).trans
                    (value_mono__p2m_a1a978aa_d041_4b6b_9848_fe8a8c0ddba8_a1
                      (V q.1) (hind q hq)))
              exact False.elim (not_lt_of_ge hbound henvy)
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hcontain
        · have hind' : ∀ q ∈ before ++ [p], A q.1 ⊆ X q.1 := by
            intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · exact hind q hq
            · have hqp : q = p := by simpa using hq
              simpa only [hqp] using hcontain
          exact ih (before ++ [p]) (by simpa [List.append_assoc] using heq) hind' r hr
  intro i hi
  have hiag : i ∈ g.1 := hag.mem_iff.mpr (by simpa using hi)
  have himap : i ∈ (g.1.zip g.2).map Prod.fst := by
    rw [List.map_fst_zip (Nat.le_of_eq hlen)]
    exact hiag
  obtain ⟨p, hp, hpi⟩ := List.mem_map.mp himap
  have hc := advance (g.1.zip g.2) [] (by simp) (by simp) p hp
  simpa only [hpi] using hc
